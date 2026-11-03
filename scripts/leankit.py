#!/usr/bin/env python3
"""leankit: checks that make a Lean formalization trustworthy, for any paper (written 2026-11-03).

Each check reads files only (the build is done by the paper's own build script; its output is an input here), so the
kit works for every paper and every build method. Subcommands:

  sources PATH...                 forbidden tokens in code (comments ignored): sorry, admit, native_decide,
                                  decide +native, axiom declarations, implemented_by, extern, unsafe, skipKernelTC
  axioms BUILD_OUT [--expect F]   parse "#print axioms" output; only propext, Classical.choice, Quot.sound allowed;
                                  with --expect LEANFILE every "#print axioms X" line of that file must be answered
  prints LEANFILE... [--printed-in F...]  every theorem declared in these main files has a "#print axioms" line,
                                  there or in F (.lean files, or theorem lists with one name per line)
  cites TEX LEANDIR...            every Lean name the paper cites in \\texttt{...} exists in the Lean sources
  spec SPECFILE                   structure of a spec file: plain definitions, equivalence theorems, restated
                                  results, sanity examples including at least one negative (not) control
  boards SPECFILE --plugin NAME   recompute every sanity example `P (![...] ...)`, `F (![...] ...) = k` in Python
                                  with plugins/NAME.py (an independent implementation of the plain definitions)
  all CONFIG                      run the checks a paper's config lists (key = value lines, see README.md)

Exit 0 when every check passes; the last line is "leankit: PASS" or "leankit: FAIL (k problems)"."""
import sys, os, re, importlib.util

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = [(r"\bsorry\b", "sorry"), (r"\badmit\b", "admit"), (r"\bnative_decide\b", "native_decide"),
             (r"decide\s*\+native", "decide +native"), (r"^\s*(private\s+|protected\s+)?axiom\s", "axiom declaration"),
             (r"implemented_by", "implemented_by"), (r"@\[\s*extern", "extern"), (r"^\s*unsafe\s", "unsafe"),
             (r"skipKernelTC", "skipKernelTC")]
HERE = os.path.dirname(os.path.abspath(__file__))


def strip_comments(text):
    """Remove /- ... -/ blocks (nested) and -- line comments; keep line numbers."""
    out, i, depth, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1; i += 2; continue
        if depth and text.startswith("-/", i):
            depth -= 1; i += 2; continue
        if depth:
            out.append("\n" if text[i] == "\n" else " "); i += 1; continue
        if text.startswith("--", i):
            j = text.find("\n", i); j = n if j < 0 else j
            out.append(" " * (j - i)); i = j; continue
        out.append(text[i]); i += 1
    return "".join(out)


def lean_files(paths):
    for p in paths:
        if os.path.isdir(p):
            for root, dirs, files in os.walk(p):
                dirs[:] = [d for d in dirs if not d.startswith(".")]
                for f in sorted(files):
                    if f.endswith(".lean"): yield os.path.join(root, f)
        elif p.endswith(".lean"): yield p


def check_sources(paths):
    probs, nfiles = [], 0
    for f in lean_files(paths):
        nfiles += 1
        for ln, line in enumerate(strip_comments(open(f, encoding="utf-8").read()).splitlines(), 1):
            for rx, what in FORBIDDEN:
                if re.search(rx, line): probs.append(f"{f}:{ln}: {what}")
    return probs, f"sources: {nfiles} files scanned"


AX_RX = re.compile(r"'([^']+)' depends on axioms: \[([^\]]*)\]")
NOAX_RX = re.compile(r"'([^']+)' does not depend on any axioms")


def parse_axioms(text):
    got = {}
    for m in AX_RX.finditer(text): got[m[1]] = {a.strip() for a in m[2].split(",") if a.strip()}
    for m in NOAX_RX.finditer(text): got[m[1]] = set()
    return got


def check_axioms(build_out, expect=None):
    text = open(build_out, encoding="utf-8", errors="replace").read(); got = parse_axioms(text); probs = []
    for name, ax in sorted(got.items()):
        bad = ax - STANDARD
        if bad: probs.append(f"{name}: non-standard axioms {sorted(bad)}")
    if re.search(r"\berror\b", text): probs.append(f"{build_out}: the build output contains 'error'")
    if expect:
        want = re.findall(r"^#print axioms\s+(\S+)", open(expect, encoding="utf-8").read(), re.M)
        for w in want:
            if w not in got: probs.append(f"{w}: no axioms answer in the build output")
    if not got: probs.append(f"{build_out}: no #print axioms output found")
    return probs, f"axioms: {len(got)} answered, standard only: {not any('non-standard' in p for p in probs)}"


DECL_RX = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma)\s+([^\s:({\[]+)", re.M)


def namespaced_decls(f):
    """(kind, full name) of theorems/lemmas in f, with namespace prefixes resolved."""
    text = strip_comments(open(f, encoding="utf-8").read()); stack, out = [], []
    for line in text.splitlines():
        m = re.match(r"^\s*namespace\s+(\S+)", line)
        if m: stack.append(m[1]); continue
        m = re.match(r"^\s*end\s+(\S+)", line)
        if m and stack and stack[-1] == m[1]: stack.pop(); continue
        m = DECL_RX.match(line)
        if m: out.append((m[1], ".".join(stack + [m[2]])))
    return out


def printed_names(paths):
    """Names printed in .lean files (#print axioms lines) or listed in theorem lists (one per line, optional 'heavy')."""
    out = set()
    for p in paths:
        t = open(p, encoding="utf-8").read()
        if p.endswith(".lean"): out |= set(re.findall(r"^#print axioms\s+(\S+)", t, re.M))
        else:
            for line in t.splitlines():
                w = line.split("#", 1)[0].split()
                if w: out.add(w[-1])
    return out


def check_prints(files, printed_in=()):
    probs, n = [], 0; extra = printed_names(printed_in)
    for f in files:
        printed = set(re.findall(r"^#print axioms\s+(\S+)", open(f, encoding="utf-8").read(), re.M)) | extra
        for kind, name in namespaced_decls(f):
            n += 1
            if name not in printed: probs.append(f"{f}: {kind} {name} has no #print axioms line")
    return probs, f"prints: {n} theorems in {len(files)} main files"


def all_decl_names(dirs):
    names = set()
    for f in lean_files(dirs):
        for _, full in namespaced_decls(f):
            parts = full.split(".")
            for k in range(len(parts)): names.add(".".join(parts[k:]))
        for m in re.finditer(r"^\s*(?:noncomputable\s+)?(?:def|abbrev|structure|instance)\s+([^\s:({\[]+)",
                             strip_comments(open(f, encoding="utf-8").read()), re.M):
            names.add(m[1])
    return names


def check_cites(tex, dirs):
    t = open(tex, encoding="utf-8").read(); names = all_decl_names(dirs); probs, n = [], 0
    files = {os.path.relpath(f, d) for d in dirs for f in lean_files([d])}
    for raw in re.findall(r"\\texttt\{([^}]*)\}", t):
        s = raw.replace("\\_", "_").strip()
        if s.endswith(".lean"):
            n += 1
            if not any(f == s or f.endswith("/" + s) or s.endswith("/" + f) for f in files):
                probs.append(f"{tex}: cites Lean file {s}, not found")
        elif re.search(r"\.(py|txt|md|tsv|csv|sh|json|pdf|tex|rs|toml|olean)$", s):
            continue
        elif re.fullmatch(r"[A-Za-z_][\w']*(\.[A-Za-z_][\w']*)*", s) and ("_" in s or "." in s):
            n += 1
            if s not in names: probs.append(f"{tex}: cites Lean name {s}, not found")
    return probs, f"cites: {n} Lean references in the paper"


def check_spec(f):
    t = open(f, encoding="utf-8").read(); code = strip_comments(t); probs = []
    defs = re.findall(r"^\s*(?:noncomputable\s+)?def\s+(\w+)", code, re.M)
    thms = [n for _, n in namespaced_decls(f)]
    eqs = [n for n in thms if re.search(r"(_iff|_eq)$", n)]
    examples = re.findall(r"^example\s*:(.*?):=", code, re.M | re.S)
    negs = [e for e in examples if "¬" in e]
    if not defs: probs.append(f"{f}: no plain definitions (def)")
    if not eqs: probs.append(f"{f}: no equivalence theorems (names ending _iff or _eq) linking plain and compact")
    if len(thms) - len(eqs) < 1: probs.append(f"{f}: no restated results")
    if not examples: probs.append(f"{f}: no sanity examples")
    if not negs: probs.append(f"{f}: no negative control example (one with ¬)")
    return probs, f"spec: {len(defs)} definitions, {len(eqs)} equivalences, {len(thms) - len(eqs)} other theorems, " \
                  f"{len(examples)} examples ({len(negs)} negative)"


VEC = r"!\[([\d,\s]+)\]"


def check_boards(f, plugin):
    spec = importlib.util.spec_from_file_location("plugin", os.path.join(HERE, "plugins", plugin + ".py"))
    P = importlib.util.module_from_spec(spec); spec.loader.exec_module(P)
    code = strip_comments(open(f, encoding="utf-8").read()); probs, n = [], 0
    for ex in re.findall(r"^example\s*:(.*?):=", code, re.M | re.S):
        for neg, name, vec in re.findall(r"(¬\s*)?(\w+)\s*\(\s*" + VEC, ex):
            if name in P.PREDICATES:
                n += 1; want = not neg; got = P.PREDICATES[name]([int(v) for v in vec.split(",")])
                if got != want: probs.append(f"{name}({vec.strip()}): Lean example says {want}, plugin says {got}")
        for name, vec, k in re.findall(r"(\w+)\s*\(\s*" + VEC + r"[^)]*\)\s*=\s*(\d+)", ex):
            if name in P.FUNCTIONS:
                n += 1; got = P.FUNCTIONS[name]([int(v) for v in vec.split(",")])
                if got != int(k): probs.append(f"{name}({vec.strip()}): Lean example says {k}, plugin says {got}")
    if n == 0: probs.append(f"{f}: no example the plugin '{plugin}' knows")
    return probs, f"boards: {n} values recomputed by plugin {plugin}"


def read_config(path):
    cfg, base = {}, os.path.dirname(os.path.abspath(path))
    for line in open(path, encoding="utf-8"):
        line = line.split("#", 1)[0].strip()
        if "=" in line:
            k, v = (s.strip() for s in line.split("=", 1)); cfg[k] = v
    absp = lambda v: [x if os.path.isabs(x) else os.path.normpath(os.path.join(base, x)) for x in v.split()]
    return cfg, absp


def run_all(path):
    cfg, absp = read_config(path); results = []
    if "sources" in cfg: results.append(check_sources(absp(cfg["sources"])))
    if "build_out" in cfg:
        outs = absp(cfg["build_out"]); exps = absp(cfg["expect"]) if "expect" in cfg else []
        if exps and len(exps) != len(outs): results.append(([f"{path}: expect must pair one Lean file per build_out"], "config"))
        for k, b in enumerate(outs): results.append(check_axioms(b, exps[k] if k < len(exps) else None))
    if "main" in cfg: results.append(check_prints(absp(cfg["main"]), absp(cfg.get("printed_in", ""))))
    if "tex" in cfg and "lean_dirs" in cfg: results.append(check_cites(absp(cfg["tex"])[0], absp(cfg["lean_dirs"])))
    if "spec" in cfg:
        results.append(check_spec(absp(cfg["spec"])[0]))
        if "plugin" in cfg: results.append(check_boards(absp(cfg["spec"])[0], cfg["plugin"]))
    return results


def report(results):
    probs = [p for r in results for p in r[0]]
    for r in results: print(("ok   " if not r[0] else "FAIL ") + r[1])
    for p in probs: print("  " + p)
    print("leankit: PASS" if not probs else f"leankit: FAIL ({len(probs)} problems)")
    return 0 if not probs else 1


def main(argv):
    if not argv or argv[0] in ("-h", "--help"): print(__doc__); return 2
    cmd, a = argv[0], argv[1:]
    if cmd == "sources": return report([check_sources(a)])
    if cmd == "axioms":
        exp = a[a.index("--expect") + 1] if "--expect" in a else None
        return report([check_axioms(a[0], exp)])
    if cmd == "prints":
        k = a.index("--printed-in") if "--printed-in" in a else len(a)
        return report([check_prints(a[:k], a[k + 1:])])
    if cmd == "cites": return report([check_cites(a[0], a[1:])])
    if cmd == "spec": return report([check_spec(a[0])])
    if cmd == "boards": return report([check_boards(a[0], a[a.index("--plugin") + 1])])
    if cmd == "all": return report(run_all(a[0]))
    print(__doc__); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
