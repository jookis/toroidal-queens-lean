import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [4, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_4_1_3_0 : go 13 7 9 [4, 1, 3, 0] = true := by decide +kernel
theorem m13_4_1_3_5 : go 13 7 9 [4, 1, 3, 5] = true := by decide +kernel
theorem m13_4_1_3_6 : go 13 7 9 [4, 1, 3, 6] = true := by decide +kernel
theorem m13_4_1_3_8 : go 13 7 9 [4, 1, 3, 8] = true := by decide +kernel
theorem m13_4_1_3_9 : go 13 7 9 [4, 1, 3, 9] = true := by decide +kernel
theorem m13_4_1_3_10 : go 13 7 9 [4, 1, 3, 10] = true := by decide +kernel
theorem m13_4_1_3_11 : go 13 7 9 [4, 1, 3, 11] = true := by decide +kernel
theorem m13_4_1_3_12 : go 13 7 9 [4, 1, 3, 12] = true := by decide +kernel

theorem m13_4_1_3 : go 13 7 10 [4, 1, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_3_5
  · exact m13_4_1_3_6
  · exact absurd hs (by decide)
  · exact m13_4_1_3_8
  · exact m13_4_1_3_9
  · exact m13_4_1_3_10
  · exact m13_4_1_3_11
  · exact m13_4_1_3_12

theorem m13_4_1_5_0 : go 13 7 9 [4, 1, 5, 0] = true := by decide +kernel
theorem m13_4_1_5_2 : go 13 7 9 [4, 1, 5, 2] = true := by decide +kernel
theorem m13_4_1_5_8 : go 13 7 9 [4, 1, 5, 8] = true := by decide +kernel
theorem m13_4_1_5_9 : go 13 7 9 [4, 1, 5, 9] = true := by decide +kernel
theorem m13_4_1_5_10 : go 13 7 9 [4, 1, 5, 10] = true := by decide +kernel
theorem m13_4_1_5_11 : go 13 7 9 [4, 1, 5, 11] = true := by decide +kernel
theorem m13_4_1_5_12 : go 13 7 9 [4, 1, 5, 12] = true := by decide +kernel

theorem m13_4_1_5 : go 13 7 10 [4, 1, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_5_0
  · exact absurd hs (by decide)
  · exact m13_4_1_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_5_8
  · exact m13_4_1_5_9
  · exact m13_4_1_5_10
  · exact m13_4_1_5_11
  · exact m13_4_1_5_12

theorem m13_4_1_7_0 : go 13 7 9 [4, 1, 7, 0] = true := by decide +kernel
theorem m13_4_1_7_2 : go 13 7 9 [4, 1, 7, 2] = true := by decide +kernel
theorem m13_4_1_7_5 : go 13 7 9 [4, 1, 7, 5] = true := by decide +kernel
theorem m13_4_1_7_9 : go 13 7 9 [4, 1, 7, 9] = true := by decide +kernel
theorem m13_4_1_7_10 : go 13 7 9 [4, 1, 7, 10] = true := by decide +kernel
theorem m13_4_1_7_11 : go 13 7 9 [4, 1, 7, 11] = true := by decide +kernel
theorem m13_4_1_7_12 : go 13 7 9 [4, 1, 7, 12] = true := by decide +kernel

theorem m13_4_1_7 : go 13 7 10 [4, 1, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_7_0
  · exact absurd hs (by decide)
  · exact m13_4_1_7_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_7_9
  · exact m13_4_1_7_10
  · exact m13_4_1_7_11
  · exact m13_4_1_7_12

theorem m13_4_1_8_0 : go 13 7 9 [4, 1, 8, 0] = true := by decide +kernel
theorem m13_4_1_8_2 : go 13 7 9 [4, 1, 8, 2] = true := by decide +kernel
theorem m13_4_1_8_5 : go 13 7 9 [4, 1, 8, 5] = true := by decide +kernel
theorem m13_4_1_8_6 : go 13 7 9 [4, 1, 8, 6] = true := by decide +kernel
theorem m13_4_1_8_10 : go 13 7 9 [4, 1, 8, 10] = true := by decide +kernel
theorem m13_4_1_8_11 : go 13 7 9 [4, 1, 8, 11] = true := by decide +kernel
theorem m13_4_1_8_12 : go 13 7 9 [4, 1, 8, 12] = true := by decide +kernel

theorem m13_4_1_8 : go 13 7 10 [4, 1, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_8_0
  · exact absurd hs (by decide)
  · exact m13_4_1_8_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_8_5
  · exact m13_4_1_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_8_10
  · exact m13_4_1_8_11
  · exact m13_4_1_8_12

theorem m13_4_1_9_0 : go 13 7 9 [4, 1, 9, 0] = true := by decide +kernel
theorem m13_4_1_9_2 : go 13 7 9 [4, 1, 9, 2] = true := by decide +kernel
theorem m13_4_1_9_5 : go 13 7 9 [4, 1, 9, 5] = true := by decide +kernel
theorem m13_4_1_9_6 : go 13 7 9 [4, 1, 9, 6] = true := by decide +kernel
theorem m13_4_1_9_11 : go 13 7 9 [4, 1, 9, 11] = true := by decide +kernel
theorem m13_4_1_9_12 : go 13 7 9 [4, 1, 9, 12] = true := by decide +kernel

theorem m13_4_1_9 : go 13 7 10 [4, 1, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_9_0
  · exact absurd hs (by decide)
  · exact m13_4_1_9_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_9_5
  · exact m13_4_1_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_9_11
  · exact m13_4_1_9_12

theorem m13_4_1_10_0 : go 13 7 9 [4, 1, 10, 0] = true := by decide +kernel
theorem m13_4_1_10_2 : go 13 7 9 [4, 1, 10, 2] = true := by decide +kernel
theorem m13_4_1_10_5 : go 13 7 9 [4, 1, 10, 5] = true := by decide +kernel
theorem m13_4_1_10_6 : go 13 7 9 [4, 1, 10, 6] = true := by decide +kernel
theorem m13_4_1_10_8 : go 13 7 9 [4, 1, 10, 8] = true := by decide +kernel
theorem m13_4_1_10_12 : go 13 7 9 [4, 1, 10, 12] = true := by decide +kernel

theorem m13_4_1_10 : go 13 7 10 [4, 1, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_10_0
  · exact absurd hs (by decide)
  · exact m13_4_1_10_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_10_5
  · exact m13_4_1_10_6
  · exact absurd hs (by decide)
  · exact m13_4_1_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_10_12

theorem m13_4_1_11_0 : go 13 7 9 [4, 1, 11, 0] = true := by decide +kernel
theorem m13_4_1_11_2 : go 13 7 9 [4, 1, 11, 2] = true := by decide +kernel
theorem m13_4_1_11_5 : go 13 7 9 [4, 1, 11, 5] = true := by decide +kernel
theorem m13_4_1_11_6 : go 13 7 9 [4, 1, 11, 6] = true := by decide +kernel
theorem m13_4_1_11_8 : go 13 7 9 [4, 1, 11, 8] = true := by decide +kernel
theorem m13_4_1_11_9 : go 13 7 9 [4, 1, 11, 9] = true := by decide +kernel

theorem m13_4_1_11 : go 13 7 10 [4, 1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_11_0
  · exact absurd hs (by decide)
  · exact m13_4_1_11_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_11_5
  · exact m13_4_1_11_6
  · exact absurd hs (by decide)
  · exact m13_4_1_11_8
  · exact m13_4_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_1_12_0 : go 13 7 9 [4, 1, 12, 0] = true := by decide +kernel
theorem m13_4_1_12_2 : go 13 7 9 [4, 1, 12, 2] = true := by decide +kernel
theorem m13_4_1_12_5 : go 13 7 9 [4, 1, 12, 5] = true := by decide +kernel
theorem m13_4_1_12_6 : go 13 7 9 [4, 1, 12, 6] = true := by decide +kernel
theorem m13_4_1_12_8 : go 13 7 9 [4, 1, 12, 8] = true := by decide +kernel
theorem m13_4_1_12_9 : go 13 7 9 [4, 1, 12, 9] = true := by decide +kernel
theorem m13_4_1_12_10 : go 13 7 9 [4, 1, 12, 10] = true := by decide +kernel

theorem m13_4_1_12 : go 13 7 10 [4, 1, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_1_12_0
  · exact absurd hs (by decide)
  · exact m13_4_1_12_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_12_5
  · exact m13_4_1_12_6
  · exact absurd hs (by decide)
  · exact m13_4_1_12_8
  · exact m13_4_1_12_9
  · exact m13_4_1_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_1 : go 13 7 11 [4, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_1_3
  · exact absurd hs (by decide)
  · exact m13_4_1_5
  · exact absurd hs (by decide)
  · exact m13_4_1_7
  · exact m13_4_1_8
  · exact m13_4_1_9
  · exact m13_4_1_10
  · exact m13_4_1_11
  · exact m13_4_1_12

end Misses
