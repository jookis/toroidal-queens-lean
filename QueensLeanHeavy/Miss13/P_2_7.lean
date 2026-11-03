import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 7]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_7_1_3 : go 13 7 9 [2, 7, 1, 3] = true := by decide +kernel
theorem m13_2_7_1_4 : go 13 7 9 [2, 7, 1, 4] = true := by decide +kernel
theorem m13_2_7_1_6 : go 13 7 9 [2, 7, 1, 6] = true := by decide +kernel
theorem m13_2_7_1_8 : go 13 7 9 [2, 7, 1, 8] = true := by decide +kernel
theorem m13_2_7_1_10 : go 13 7 9 [2, 7, 1, 10] = true := by decide +kernel
theorem m13_2_7_1_11 : go 13 7 9 [2, 7, 1, 11] = true := by decide +kernel
theorem m13_2_7_1_12 : go 13 7 9 [2, 7, 1, 12] = true := by decide +kernel

theorem m13_2_7_1 : go 13 7 10 [2, 7, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_7_1_3
  · exact m13_2_7_1_4
  · exact absurd hs (by decide)
  · exact m13_2_7_1_6
  · exact absurd hs (by decide)
  · exact m13_2_7_1_8
  · exact absurd hs (by decide)
  · exact m13_2_7_1_10
  · exact m13_2_7_1_11
  · exact m13_2_7_1_12

theorem m13_2_7_3_0 : go 13 7 9 [2, 7, 3, 0] = true := by decide +kernel
theorem m13_2_7_3_1 : go 13 7 9 [2, 7, 3, 1] = true := by decide +kernel
theorem m13_2_7_3_6 : go 13 7 9 [2, 7, 3, 6] = true := by decide +kernel
theorem m13_2_7_3_8 : go 13 7 9 [2, 7, 3, 8] = true := by decide +kernel
theorem m13_2_7_3_10 : go 13 7 9 [2, 7, 3, 10] = true := by decide +kernel
theorem m13_2_7_3_11 : go 13 7 9 [2, 7, 3, 11] = true := by decide +kernel
theorem m13_2_7_3_12 : go 13 7 9 [2, 7, 3, 12] = true := by decide +kernel

theorem m13_2_7_3 : go 13 7 10 [2, 7, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_7_3_0
  · exact m13_2_7_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_7_3_6
  · exact absurd hs (by decide)
  · exact m13_2_7_3_8
  · exact absurd hs (by decide)
  · exact m13_2_7_3_10
  · exact m13_2_7_3_11
  · exact m13_2_7_3_12

theorem m13_2_7_5_0 : go 13 7 9 [2, 7, 5, 0] = true := by decide +kernel
theorem m13_2_7_5_1 : go 13 7 9 [2, 7, 5, 1] = true := by decide +kernel
theorem m13_2_7_5_3 : go 13 7 9 [2, 7, 5, 3] = true := by decide +kernel
theorem m13_2_7_5_8 : go 13 7 9 [2, 7, 5, 8] = true := by decide +kernel
theorem m13_2_7_5_10 : go 13 7 9 [2, 7, 5, 10] = true := by decide +kernel
theorem m13_2_7_5_11 : go 13 7 9 [2, 7, 5, 11] = true := by decide +kernel
theorem m13_2_7_5_12 : go 13 7 9 [2, 7, 5, 12] = true := by decide +kernel

theorem m13_2_7_5 : go 13 7 10 [2, 7, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_7_5_0
  · exact m13_2_7_5_1
  · exact absurd hs (by decide)
  · exact m13_2_7_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_7_5_8
  · exact absurd hs (by decide)
  · exact m13_2_7_5_10
  · exact m13_2_7_5_11
  · exact m13_2_7_5_12

theorem m13_2_7_9_0 : go 13 7 9 [2, 7, 9, 0] = true := by decide +kernel
theorem m13_2_7_9_1 : go 13 7 9 [2, 7, 9, 1] = true := by decide +kernel
theorem m13_2_7_9_3 : go 13 7 9 [2, 7, 9, 3] = true := by decide +kernel
theorem m13_2_7_9_4 : go 13 7 9 [2, 7, 9, 4] = true := by decide +kernel
theorem m13_2_7_9_6 : go 13 7 9 [2, 7, 9, 6] = true := by decide +kernel
theorem m13_2_7_9_11 : go 13 7 9 [2, 7, 9, 11] = true := by decide +kernel
theorem m13_2_7_9_12 : go 13 7 9 [2, 7, 9, 12] = true := by decide +kernel

theorem m13_2_7_9 : go 13 7 10 [2, 7, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_7_9_0
  · exact m13_2_7_9_1
  · exact absurd hs (by decide)
  · exact m13_2_7_9_3
  · exact m13_2_7_9_4
  · exact absurd hs (by decide)
  · exact m13_2_7_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_7_9_11
  · exact m13_2_7_9_12

theorem m13_2_7_10_0 : go 13 7 9 [2, 7, 10, 0] = true := by decide +kernel
theorem m13_2_7_10_1 : go 13 7 9 [2, 7, 10, 1] = true := by decide +kernel
theorem m13_2_7_10_3 : go 13 7 9 [2, 7, 10, 3] = true := by decide +kernel
theorem m13_2_7_10_4 : go 13 7 9 [2, 7, 10, 4] = true := by decide +kernel
theorem m13_2_7_10_6 : go 13 7 9 [2, 7, 10, 6] = true := by decide +kernel
theorem m13_2_7_10_8 : go 13 7 9 [2, 7, 10, 8] = true := by decide +kernel
theorem m13_2_7_10_12 : go 13 7 9 [2, 7, 10, 12] = true := by decide +kernel

theorem m13_2_7_10 : go 13 7 10 [2, 7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_7_10_0
  · exact m13_2_7_10_1
  · exact absurd hs (by decide)
  · exact m13_2_7_10_3
  · exact m13_2_7_10_4
  · exact absurd hs (by decide)
  · exact m13_2_7_10_6
  · exact absurd hs (by decide)
  · exact m13_2_7_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_7_10_12

theorem m13_2_7_11_0 : go 13 7 9 [2, 7, 11, 0] = true := by decide +kernel
theorem m13_2_7_11_1 : go 13 7 9 [2, 7, 11, 1] = true := by decide +kernel
theorem m13_2_7_11_3 : go 13 7 9 [2, 7, 11, 3] = true := by decide +kernel
theorem m13_2_7_11_4 : go 13 7 9 [2, 7, 11, 4] = true := by decide +kernel
theorem m13_2_7_11_6 : go 13 7 9 [2, 7, 11, 6] = true := by decide +kernel
theorem m13_2_7_11_8 : go 13 7 9 [2, 7, 11, 8] = true := by decide +kernel

theorem m13_2_7_11 : go 13 7 10 [2, 7, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_7_11_0
  · exact m13_2_7_11_1
  · exact absurd hs (by decide)
  · exact m13_2_7_11_3
  · exact m13_2_7_11_4
  · exact absurd hs (by decide)
  · exact m13_2_7_11_6
  · exact absurd hs (by decide)
  · exact m13_2_7_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_7_12_0 : go 13 7 9 [2, 7, 12, 0] = true := by decide +kernel
theorem m13_2_7_12_1 : go 13 7 9 [2, 7, 12, 1] = true := by decide +kernel
theorem m13_2_7_12_3 : go 13 7 9 [2, 7, 12, 3] = true := by decide +kernel
theorem m13_2_7_12_4 : go 13 7 9 [2, 7, 12, 4] = true := by decide +kernel
theorem m13_2_7_12_6 : go 13 7 9 [2, 7, 12, 6] = true := by decide +kernel
theorem m13_2_7_12_8 : go 13 7 9 [2, 7, 12, 8] = true := by decide +kernel
theorem m13_2_7_12_10 : go 13 7 9 [2, 7, 12, 10] = true := by decide +kernel

theorem m13_2_7_12 : go 13 7 10 [2, 7, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_7_12_0
  · exact m13_2_7_12_1
  · exact absurd hs (by decide)
  · exact m13_2_7_12_3
  · exact m13_2_7_12_4
  · exact absurd hs (by decide)
  · exact m13_2_7_12_6
  · exact absurd hs (by decide)
  · exact m13_2_7_12_8
  · exact absurd hs (by decide)
  · exact m13_2_7_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_7 : go 13 7 11 [2, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_7_1
  · exact absurd hs (by decide)
  · exact m13_2_7_3
  · exact absurd hs (by decide)
  · exact m13_2_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_7_9
  · exact m13_2_7_10
  · exact m13_2_7_11
  · exact m13_2_7_12

end Misses
