import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [6, 2]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_6_2_0_5 : go 13 7 9 [6, 2, 0, 5] = true := by decide +kernel
theorem m13_6_2_0_7 : go 13 7 9 [6, 2, 0, 7] = true := by decide +kernel
theorem m13_6_2_0_8 : go 13 7 9 [6, 2, 0, 8] = true := by decide +kernel
theorem m13_6_2_0_10 : go 13 7 9 [6, 2, 0, 10] = true := by decide +kernel
theorem m13_6_2_0_11 : go 13 7 9 [6, 2, 0, 11] = true := by decide +kernel
theorem m13_6_2_0_12 : go 13 7 9 [6, 2, 0, 12] = true := by decide +kernel

theorem m13_6_2_0 : go 13 7 10 [6, 2, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_0_5
  · exact absurd hs (by decide)
  · exact m13_6_2_0_7
  · exact m13_6_2_0_8
  · exact absurd hs (by decide)
  · exact m13_6_2_0_10
  · exact m13_6_2_0_11
  · exact m13_6_2_0_12

theorem m13_6_2_5_1 : go 13 7 9 [6, 2, 5, 1] = true := by decide +kernel
theorem m13_6_2_5_7 : go 13 7 9 [6, 2, 5, 7] = true := by decide +kernel
theorem m13_6_2_5_8 : go 13 7 9 [6, 2, 5, 8] = true := by decide +kernel
theorem m13_6_2_5_10 : go 13 7 9 [6, 2, 5, 10] = true := by decide +kernel
theorem m13_6_2_5_11 : go 13 7 9 [6, 2, 5, 11] = true := by decide +kernel
theorem m13_6_2_5_12 : go 13 7 9 [6, 2, 5, 12] = true := by decide +kernel

theorem m13_6_2_5 : go 13 7 10 [6, 2, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_2_5_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_5_7
  · exact m13_6_2_5_8
  · exact absurd hs (by decide)
  · exact m13_6_2_5_10
  · exact m13_6_2_5_11
  · exact m13_6_2_5_12

theorem m13_6_2_7_1 : go 13 7 9 [6, 2, 7, 1] = true := by decide +kernel
theorem m13_6_2_7_5 : go 13 7 9 [6, 2, 7, 5] = true := by decide +kernel
theorem m13_6_2_7_10 : go 13 7 9 [6, 2, 7, 10] = true := by decide +kernel
theorem m13_6_2_7_11 : go 13 7 9 [6, 2, 7, 11] = true := by decide +kernel
theorem m13_6_2_7_12 : go 13 7 9 [6, 2, 7, 12] = true := by decide +kernel

theorem m13_6_2_7 : go 13 7 10 [6, 2, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_2_7_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_7_10
  · exact m13_6_2_7_11
  · exact m13_6_2_7_12

theorem m13_6_2_9_1 : go 13 7 9 [6, 2, 9, 1] = true := by decide +kernel
theorem m13_6_2_9_5 : go 13 7 9 [6, 2, 9, 5] = true := by decide +kernel
theorem m13_6_2_9_7 : go 13 7 9 [6, 2, 9, 7] = true := by decide +kernel
theorem m13_6_2_9_11 : go 13 7 9 [6, 2, 9, 11] = true := by decide +kernel
theorem m13_6_2_9_12 : go 13 7 9 [6, 2, 9, 12] = true := by decide +kernel

theorem m13_6_2_9 : go 13 7 10 [6, 2, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_2_9_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_9_5
  · exact absurd hs (by decide)
  · exact m13_6_2_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_9_11
  · exact m13_6_2_9_12

theorem m13_6_2_10_1 : go 13 7 9 [6, 2, 10, 1] = true := by decide +kernel
theorem m13_6_2_10_5 : go 13 7 9 [6, 2, 10, 5] = true := by decide +kernel
theorem m13_6_2_10_7 : go 13 7 9 [6, 2, 10, 7] = true := by decide +kernel
theorem m13_6_2_10_8 : go 13 7 9 [6, 2, 10, 8] = true := by decide +kernel
theorem m13_6_2_10_12 : go 13 7 9 [6, 2, 10, 12] = true := by decide +kernel

theorem m13_6_2_10 : go 13 7 10 [6, 2, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_2_10_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_10_5
  · exact absurd hs (by decide)
  · exact m13_6_2_10_7
  · exact m13_6_2_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_10_12

theorem m13_6_2_11_1 : go 13 7 9 [6, 2, 11, 1] = true := by decide +kernel
theorem m13_6_2_11_5 : go 13 7 9 [6, 2, 11, 5] = true := by decide +kernel
theorem m13_6_2_11_7 : go 13 7 9 [6, 2, 11, 7] = true := by decide +kernel
theorem m13_6_2_11_8 : go 13 7 9 [6, 2, 11, 8] = true := by decide +kernel

theorem m13_6_2_11 : go 13 7 10 [6, 2, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_2_11_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_11_5
  · exact absurd hs (by decide)
  · exact m13_6_2_11_7
  · exact m13_6_2_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_2_12_1 : go 13 7 9 [6, 2, 12, 1] = true := by decide +kernel
theorem m13_6_2_12_5 : go 13 7 9 [6, 2, 12, 5] = true := by decide +kernel
theorem m13_6_2_12_7 : go 13 7 9 [6, 2, 12, 7] = true := by decide +kernel
theorem m13_6_2_12_8 : go 13 7 9 [6, 2, 12, 8] = true := by decide +kernel
theorem m13_6_2_12_10 : go 13 7 9 [6, 2, 12, 10] = true := by decide +kernel

theorem m13_6_2_12 : go 13 7 10 [6, 2, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_2_12_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_12_5
  · exact absurd hs (by decide)
  · exact m13_6_2_12_7
  · exact m13_6_2_12_8
  · exact absurd hs (by decide)
  · exact m13_6_2_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_2 : go 13 7 11 [6, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_2_5
  · exact absurd hs (by decide)
  · exact m13_6_2_7
  · exact absurd hs (by decide)
  · exact m13_6_2_9
  · exact m13_6_2_10
  · exact m13_6_2_11
  · exact m13_6_2_12

end Misses
