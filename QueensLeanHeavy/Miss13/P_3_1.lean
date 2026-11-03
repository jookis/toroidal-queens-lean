import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_1_4_2 : go 13 7 9 [3, 1, 4, 2] = true := by decide +kernel
theorem m13_3_1_4_7 : go 13 7 9 [3, 1, 4, 7] = true := by decide +kernel
theorem m13_3_1_4_8 : go 13 7 9 [3, 1, 4, 8] = true := by decide +kernel
theorem m13_3_1_4_9 : go 13 7 9 [3, 1, 4, 9] = true := by decide +kernel
theorem m13_3_1_4_10 : go 13 7 9 [3, 1, 4, 10] = true := by decide +kernel
theorem m13_3_1_4_11 : go 13 7 9 [3, 1, 4, 11] = true := by decide +kernel
theorem m13_3_1_4_12 : go 13 7 9 [3, 1, 4, 12] = true := by decide +kernel

theorem m13_3_1_4 : go 13 7 10 [3, 1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_4_7
  · exact m13_3_1_4_8
  · exact m13_3_1_4_9
  · exact m13_3_1_4_10
  · exact m13_3_1_4_11
  · exact m13_3_1_4_12

theorem m13_3_1_6_2 : go 13 7 9 [3, 1, 6, 2] = true := by decide +kernel
theorem m13_3_1_6_4 : go 13 7 9 [3, 1, 6, 4] = true := by decide +kernel
theorem m13_3_1_6_8 : go 13 7 9 [3, 1, 6, 8] = true := by decide +kernel
theorem m13_3_1_6_9 : go 13 7 9 [3, 1, 6, 9] = true := by decide +kernel
theorem m13_3_1_6_10 : go 13 7 9 [3, 1, 6, 10] = true := by decide +kernel
theorem m13_3_1_6_11 : go 13 7 9 [3, 1, 6, 11] = true := by decide +kernel
theorem m13_3_1_6_12 : go 13 7 9 [3, 1, 6, 12] = true := by decide +kernel

theorem m13_3_1_6 : go 13 7 10 [3, 1, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_6_2
  · exact absurd hs (by decide)
  · exact m13_3_1_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_6_8
  · exact m13_3_1_6_9
  · exact m13_3_1_6_10
  · exact m13_3_1_6_11
  · exact m13_3_1_6_12

theorem m13_3_1_7_2 : go 13 7 9 [3, 1, 7, 2] = true := by decide +kernel
theorem m13_3_1_7_4 : go 13 7 9 [3, 1, 7, 4] = true := by decide +kernel
theorem m13_3_1_7_5 : go 13 7 9 [3, 1, 7, 5] = true := by decide +kernel
theorem m13_3_1_7_9 : go 13 7 9 [3, 1, 7, 9] = true := by decide +kernel
theorem m13_3_1_7_10 : go 13 7 9 [3, 1, 7, 10] = true := by decide +kernel
theorem m13_3_1_7_11 : go 13 7 9 [3, 1, 7, 11] = true := by decide +kernel
theorem m13_3_1_7_12 : go 13 7 9 [3, 1, 7, 12] = true := by decide +kernel

theorem m13_3_1_7 : go 13 7 10 [3, 1, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_7_2
  · exact absurd hs (by decide)
  · exact m13_3_1_7_4
  · exact m13_3_1_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_7_9
  · exact m13_3_1_7_10
  · exact m13_3_1_7_11
  · exact m13_3_1_7_12

theorem m13_3_1_8_2 : go 13 7 9 [3, 1, 8, 2] = true := by decide +kernel
theorem m13_3_1_8_4 : go 13 7 9 [3, 1, 8, 4] = true := by decide +kernel
theorem m13_3_1_8_5 : go 13 7 9 [3, 1, 8, 5] = true := by decide +kernel
theorem m13_3_1_8_10 : go 13 7 9 [3, 1, 8, 10] = true := by decide +kernel
theorem m13_3_1_8_11 : go 13 7 9 [3, 1, 8, 11] = true := by decide +kernel
theorem m13_3_1_8_12 : go 13 7 9 [3, 1, 8, 12] = true := by decide +kernel

theorem m13_3_1_8 : go 13 7 10 [3, 1, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_8_2
  · exact absurd hs (by decide)
  · exact m13_3_1_8_4
  · exact m13_3_1_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_8_10
  · exact m13_3_1_8_11
  · exact m13_3_1_8_12

theorem m13_3_1_9_2 : go 13 7 9 [3, 1, 9, 2] = true := by decide +kernel
theorem m13_3_1_9_4 : go 13 7 9 [3, 1, 9, 4] = true := by decide +kernel
theorem m13_3_1_9_5 : go 13 7 9 [3, 1, 9, 5] = true := by decide +kernel
theorem m13_3_1_9_7 : go 13 7 9 [3, 1, 9, 7] = true := by decide +kernel
theorem m13_3_1_9_11 : go 13 7 9 [3, 1, 9, 11] = true := by decide +kernel
theorem m13_3_1_9_12 : go 13 7 9 [3, 1, 9, 12] = true := by decide +kernel

theorem m13_3_1_9 : go 13 7 10 [3, 1, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_9_2
  · exact absurd hs (by decide)
  · exact m13_3_1_9_4
  · exact m13_3_1_9_5
  · exact absurd hs (by decide)
  · exact m13_3_1_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_9_11
  · exact m13_3_1_9_12

theorem m13_3_1_10_2 : go 13 7 9 [3, 1, 10, 2] = true := by decide +kernel
theorem m13_3_1_10_4 : go 13 7 9 [3, 1, 10, 4] = true := by decide +kernel
theorem m13_3_1_10_5 : go 13 7 9 [3, 1, 10, 5] = true := by decide +kernel
theorem m13_3_1_10_7 : go 13 7 9 [3, 1, 10, 7] = true := by decide +kernel
theorem m13_3_1_10_8 : go 13 7 9 [3, 1, 10, 8] = true := by decide +kernel
theorem m13_3_1_10_12 : go 13 7 9 [3, 1, 10, 12] = true := by decide +kernel

theorem m13_3_1_10 : go 13 7 10 [3, 1, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_10_2
  · exact absurd hs (by decide)
  · exact m13_3_1_10_4
  · exact m13_3_1_10_5
  · exact absurd hs (by decide)
  · exact m13_3_1_10_7
  · exact m13_3_1_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_10_12

theorem m13_3_1_11_2 : go 13 7 9 [3, 1, 11, 2] = true := by decide +kernel
theorem m13_3_1_11_4 : go 13 7 9 [3, 1, 11, 4] = true := by decide +kernel
theorem m13_3_1_11_5 : go 13 7 9 [3, 1, 11, 5] = true := by decide +kernel
theorem m13_3_1_11_7 : go 13 7 9 [3, 1, 11, 7] = true := by decide +kernel
theorem m13_3_1_11_8 : go 13 7 9 [3, 1, 11, 8] = true := by decide +kernel
theorem m13_3_1_11_9 : go 13 7 9 [3, 1, 11, 9] = true := by decide +kernel

theorem m13_3_1_11 : go 13 7 10 [3, 1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_11_2
  · exact absurd hs (by decide)
  · exact m13_3_1_11_4
  · exact m13_3_1_11_5
  · exact absurd hs (by decide)
  · exact m13_3_1_11_7
  · exact m13_3_1_11_8
  · exact m13_3_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_1_12_2 : go 13 7 9 [3, 1, 12, 2] = true := by decide +kernel
theorem m13_3_1_12_4 : go 13 7 9 [3, 1, 12, 4] = true := by decide +kernel
theorem m13_3_1_12_5 : go 13 7 9 [3, 1, 12, 5] = true := by decide +kernel
theorem m13_3_1_12_7 : go 13 7 9 [3, 1, 12, 7] = true := by decide +kernel
theorem m13_3_1_12_8 : go 13 7 9 [3, 1, 12, 8] = true := by decide +kernel
theorem m13_3_1_12_9 : go 13 7 9 [3, 1, 12, 9] = true := by decide +kernel
theorem m13_3_1_12_10 : go 13 7 9 [3, 1, 12, 10] = true := by decide +kernel

theorem m13_3_1_12 : go 13 7 10 [3, 1, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_12_2
  · exact absurd hs (by decide)
  · exact m13_3_1_12_4
  · exact m13_3_1_12_5
  · exact absurd hs (by decide)
  · exact m13_3_1_12_7
  · exact m13_3_1_12_8
  · exact m13_3_1_12_9
  · exact m13_3_1_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_1 : go 13 7 11 [3, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_1_4
  · exact absurd hs (by decide)
  · exact m13_3_1_6
  · exact m13_3_1_7
  · exact m13_3_1_8
  · exact m13_3_1_9
  · exact m13_3_1_10
  · exact m13_3_1_11
  · exact m13_3_1_12

end Misses
