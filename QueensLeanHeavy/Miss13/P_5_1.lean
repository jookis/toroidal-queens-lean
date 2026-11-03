import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [5, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_5_1_4_0 : go 13 7 9 [5, 1, 4, 0] = true := by decide +kernel
theorem m13_5_1_4_6 : go 13 7 9 [5, 1, 4, 6] = true := by decide +kernel
theorem m13_5_1_4_7 : go 13 7 9 [5, 1, 4, 7] = true := by decide +kernel
theorem m13_5_1_4_9 : go 13 7 9 [5, 1, 4, 9] = true := by decide +kernel
theorem m13_5_1_4_10 : go 13 7 9 [5, 1, 4, 10] = true := by decide +kernel
theorem m13_5_1_4_11 : go 13 7 9 [5, 1, 4, 11] = true := by decide +kernel
theorem m13_5_1_4_12 : go 13 7 9 [5, 1, 4, 12] = true := by decide +kernel

theorem m13_5_1_4 : go 13 7 10 [5, 1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_4_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_4_6
  · exact m13_5_1_4_7
  · exact absurd hs (by decide)
  · exact m13_5_1_4_9
  · exact m13_5_1_4_10
  · exact m13_5_1_4_11
  · exact m13_5_1_4_12

theorem m13_5_1_6_0 : go 13 7 9 [5, 1, 6, 0] = true := by decide +kernel
theorem m13_5_1_6_4 : go 13 7 9 [5, 1, 6, 4] = true := by decide +kernel
theorem m13_5_1_6_9 : go 13 7 9 [5, 1, 6, 9] = true := by decide +kernel
theorem m13_5_1_6_10 : go 13 7 9 [5, 1, 6, 10] = true := by decide +kernel
theorem m13_5_1_6_11 : go 13 7 9 [5, 1, 6, 11] = true := by decide +kernel
theorem m13_5_1_6_12 : go 13 7 9 [5, 1, 6, 12] = true := by decide +kernel

theorem m13_5_1_6 : go 13 7 10 [5, 1, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_6_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_6_9
  · exact m13_5_1_6_10
  · exact m13_5_1_6_11
  · exact m13_5_1_6_12

theorem m13_5_1_8_0 : go 13 7 9 [5, 1, 8, 0] = true := by decide +kernel
theorem m13_5_1_8_4 : go 13 7 9 [5, 1, 8, 4] = true := by decide +kernel
theorem m13_5_1_8_6 : go 13 7 9 [5, 1, 8, 6] = true := by decide +kernel
theorem m13_5_1_8_10 : go 13 7 9 [5, 1, 8, 10] = true := by decide +kernel
theorem m13_5_1_8_11 : go 13 7 9 [5, 1, 8, 11] = true := by decide +kernel
theorem m13_5_1_8_12 : go 13 7 9 [5, 1, 8, 12] = true := by decide +kernel

theorem m13_5_1_8 : go 13 7 10 [5, 1, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_8_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_8_4
  · exact absurd hs (by decide)
  · exact m13_5_1_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_8_10
  · exact m13_5_1_8_11
  · exact m13_5_1_8_12

theorem m13_5_1_9_0 : go 13 7 9 [5, 1, 9, 0] = true := by decide +kernel
theorem m13_5_1_9_4 : go 13 7 9 [5, 1, 9, 4] = true := by decide +kernel
theorem m13_5_1_9_6 : go 13 7 9 [5, 1, 9, 6] = true := by decide +kernel
theorem m13_5_1_9_7 : go 13 7 9 [5, 1, 9, 7] = true := by decide +kernel
theorem m13_5_1_9_11 : go 13 7 9 [5, 1, 9, 11] = true := by decide +kernel
theorem m13_5_1_9_12 : go 13 7 9 [5, 1, 9, 12] = true := by decide +kernel

theorem m13_5_1_9 : go 13 7 10 [5, 1, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_9_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_9_4
  · exact absurd hs (by decide)
  · exact m13_5_1_9_6
  · exact m13_5_1_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_9_11
  · exact m13_5_1_9_12

theorem m13_5_1_10_0 : go 13 7 9 [5, 1, 10, 0] = true := by decide +kernel
theorem m13_5_1_10_4 : go 13 7 9 [5, 1, 10, 4] = true := by decide +kernel
theorem m13_5_1_10_6 : go 13 7 9 [5, 1, 10, 6] = true := by decide +kernel
theorem m13_5_1_10_7 : go 13 7 9 [5, 1, 10, 7] = true := by decide +kernel
theorem m13_5_1_10_12 : go 13 7 9 [5, 1, 10, 12] = true := by decide +kernel

theorem m13_5_1_10 : go 13 7 10 [5, 1, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_10_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_10_4
  · exact absurd hs (by decide)
  · exact m13_5_1_10_6
  · exact m13_5_1_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_10_12

theorem m13_5_1_11_0 : go 13 7 9 [5, 1, 11, 0] = true := by decide +kernel
theorem m13_5_1_11_4 : go 13 7 9 [5, 1, 11, 4] = true := by decide +kernel
theorem m13_5_1_11_6 : go 13 7 9 [5, 1, 11, 6] = true := by decide +kernel
theorem m13_5_1_11_7 : go 13 7 9 [5, 1, 11, 7] = true := by decide +kernel
theorem m13_5_1_11_9 : go 13 7 9 [5, 1, 11, 9] = true := by decide +kernel

theorem m13_5_1_11 : go 13 7 10 [5, 1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_11_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_11_4
  · exact absurd hs (by decide)
  · exact m13_5_1_11_6
  · exact m13_5_1_11_7
  · exact absurd hs (by decide)
  · exact m13_5_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_1_12_0 : go 13 7 9 [5, 1, 12, 0] = true := by decide +kernel
theorem m13_5_1_12_4 : go 13 7 9 [5, 1, 12, 4] = true := by decide +kernel
theorem m13_5_1_12_6 : go 13 7 9 [5, 1, 12, 6] = true := by decide +kernel
theorem m13_5_1_12_7 : go 13 7 9 [5, 1, 12, 7] = true := by decide +kernel
theorem m13_5_1_12_9 : go 13 7 9 [5, 1, 12, 9] = true := by decide +kernel
theorem m13_5_1_12_10 : go 13 7 9 [5, 1, 12, 10] = true := by decide +kernel

theorem m13_5_1_12 : go 13 7 10 [5, 1, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_1_12_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_12_4
  · exact absurd hs (by decide)
  · exact m13_5_1_12_6
  · exact m13_5_1_12_7
  · exact absurd hs (by decide)
  · exact m13_5_1_12_9
  · exact m13_5_1_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_1 : go 13 7 11 [5, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_1_4
  · exact absurd hs (by decide)
  · exact m13_5_1_6
  · exact absurd hs (by decide)
  · exact m13_5_1_8
  · exact m13_5_1_9
  · exact m13_5_1_10
  · exact m13_5_1_11
  · exact m13_5_1_12

end Misses
