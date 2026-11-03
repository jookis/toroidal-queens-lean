import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 9]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_9_1_3 : go 13 7 9 [2, 9, 1, 3] = true := by decide +kernel
theorem m13_2_9_1_4 : go 13 7 9 [2, 9, 1, 4] = true := by decide +kernel
theorem m13_2_9_1_6 : go 13 7 9 [2, 9, 1, 6] = true := by decide +kernel
theorem m13_2_9_1_8 : go 13 7 9 [2, 9, 1, 8] = true := by decide +kernel
theorem m13_2_9_1_10 : go 13 7 9 [2, 9, 1, 10] = true := by decide +kernel
theorem m13_2_9_1_12 : go 13 7 9 [2, 9, 1, 12] = true := by decide +kernel

theorem m13_2_9_1 : go 13 7 10 [2, 9, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_9_1_3
  · exact m13_2_9_1_4
  · exact absurd hs (by decide)
  · exact m13_2_9_1_6
  · exact absurd hs (by decide)
  · exact m13_2_9_1_8
  · exact absurd hs (by decide)
  · exact m13_2_9_1_10
  · exact absurd hs (by decide)
  · exact m13_2_9_1_12

theorem m13_2_9_3_0 : go 13 7 9 [2, 9, 3, 0] = true := by decide +kernel
theorem m13_2_9_3_1 : go 13 7 9 [2, 9, 3, 1] = true := by decide +kernel
theorem m13_2_9_3_6 : go 13 7 9 [2, 9, 3, 6] = true := by decide +kernel
theorem m13_2_9_3_8 : go 13 7 9 [2, 9, 3, 8] = true := by decide +kernel
theorem m13_2_9_3_10 : go 13 7 9 [2, 9, 3, 10] = true := by decide +kernel
theorem m13_2_9_3_12 : go 13 7 9 [2, 9, 3, 12] = true := by decide +kernel

theorem m13_2_9_3 : go 13 7 10 [2, 9, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_9_3_0
  · exact m13_2_9_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_9_3_6
  · exact absurd hs (by decide)
  · exact m13_2_9_3_8
  · exact absurd hs (by decide)
  · exact m13_2_9_3_10
  · exact absurd hs (by decide)
  · exact m13_2_9_3_12

theorem m13_2_9_5_0 : go 13 7 9 [2, 9, 5, 0] = true := by decide +kernel
theorem m13_2_9_5_1 : go 13 7 9 [2, 9, 5, 1] = true := by decide +kernel
theorem m13_2_9_5_3 : go 13 7 9 [2, 9, 5, 3] = true := by decide +kernel
theorem m13_2_9_5_8 : go 13 7 9 [2, 9, 5, 8] = true := by decide +kernel
theorem m13_2_9_5_10 : go 13 7 9 [2, 9, 5, 10] = true := by decide +kernel
theorem m13_2_9_5_12 : go 13 7 9 [2, 9, 5, 12] = true := by decide +kernel

theorem m13_2_9_5 : go 13 7 10 [2, 9, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_9_5_0
  · exact m13_2_9_5_1
  · exact absurd hs (by decide)
  · exact m13_2_9_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_9_5_8
  · exact absurd hs (by decide)
  · exact m13_2_9_5_10
  · exact absurd hs (by decide)
  · exact m13_2_9_5_12

theorem m13_2_9_6_0 : go 13 7 9 [2, 9, 6, 0] = true := by decide +kernel
theorem m13_2_9_6_1 : go 13 7 9 [2, 9, 6, 1] = true := by decide +kernel
theorem m13_2_9_6_3 : go 13 7 9 [2, 9, 6, 3] = true := by decide +kernel
theorem m13_2_9_6_4 : go 13 7 9 [2, 9, 6, 4] = true := by decide +kernel
theorem m13_2_9_6_8 : go 13 7 9 [2, 9, 6, 8] = true := by decide +kernel
theorem m13_2_9_6_10 : go 13 7 9 [2, 9, 6, 10] = true := by decide +kernel
theorem m13_2_9_6_12 : go 13 7 9 [2, 9, 6, 12] = true := by decide +kernel

theorem m13_2_9_6 : go 13 7 10 [2, 9, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_9_6_0
  · exact m13_2_9_6_1
  · exact absurd hs (by decide)
  · exact m13_2_9_6_3
  · exact m13_2_9_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_9_6_8
  · exact absurd hs (by decide)
  · exact m13_2_9_6_10
  · exact absurd hs (by decide)
  · exact m13_2_9_6_12

theorem m13_2_9_7_0 : go 13 7 9 [2, 9, 7, 0] = true := by decide +kernel
theorem m13_2_9_7_1 : go 13 7 9 [2, 9, 7, 1] = true := by decide +kernel
theorem m13_2_9_7_3 : go 13 7 9 [2, 9, 7, 3] = true := by decide +kernel
theorem m13_2_9_7_4 : go 13 7 9 [2, 9, 7, 4] = true := by decide +kernel
theorem m13_2_9_7_10 : go 13 7 9 [2, 9, 7, 10] = true := by decide +kernel
theorem m13_2_9_7_12 : go 13 7 9 [2, 9, 7, 12] = true := by decide +kernel

theorem m13_2_9_7 : go 13 7 10 [2, 9, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_9_7_0
  · exact m13_2_9_7_1
  · exact absurd hs (by decide)
  · exact m13_2_9_7_3
  · exact m13_2_9_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_9_7_10
  · exact absurd hs (by decide)
  · exact m13_2_9_7_12

theorem m13_2_9_11_0 : go 13 7 9 [2, 9, 11, 0] = true := by decide +kernel
theorem m13_2_9_11_1 : go 13 7 9 [2, 9, 11, 1] = true := by decide +kernel
theorem m13_2_9_11_3 : go 13 7 9 [2, 9, 11, 3] = true := by decide +kernel
theorem m13_2_9_11_4 : go 13 7 9 [2, 9, 11, 4] = true := by decide +kernel
theorem m13_2_9_11_6 : go 13 7 9 [2, 9, 11, 6] = true := by decide +kernel
theorem m13_2_9_11_8 : go 13 7 9 [2, 9, 11, 8] = true := by decide +kernel

theorem m13_2_9_11 : go 13 7 10 [2, 9, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_9_11_0
  · exact m13_2_9_11_1
  · exact absurd hs (by decide)
  · exact m13_2_9_11_3
  · exact m13_2_9_11_4
  · exact absurd hs (by decide)
  · exact m13_2_9_11_6
  · exact absurd hs (by decide)
  · exact m13_2_9_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_9_12_0 : go 13 7 9 [2, 9, 12, 0] = true := by decide +kernel
theorem m13_2_9_12_1 : go 13 7 9 [2, 9, 12, 1] = true := by decide +kernel
theorem m13_2_9_12_3 : go 13 7 9 [2, 9, 12, 3] = true := by decide +kernel
theorem m13_2_9_12_4 : go 13 7 9 [2, 9, 12, 4] = true := by decide +kernel
theorem m13_2_9_12_6 : go 13 7 9 [2, 9, 12, 6] = true := by decide +kernel
theorem m13_2_9_12_8 : go 13 7 9 [2, 9, 12, 8] = true := by decide +kernel
theorem m13_2_9_12_10 : go 13 7 9 [2, 9, 12, 10] = true := by decide +kernel

theorem m13_2_9_12 : go 13 7 10 [2, 9, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_9_12_0
  · exact m13_2_9_12_1
  · exact absurd hs (by decide)
  · exact m13_2_9_12_3
  · exact m13_2_9_12_4
  · exact absurd hs (by decide)
  · exact m13_2_9_12_6
  · exact absurd hs (by decide)
  · exact m13_2_9_12_8
  · exact absurd hs (by decide)
  · exact m13_2_9_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_9 : go 13 7 11 [2, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_9_1
  · exact absurd hs (by decide)
  · exact m13_2_9_3
  · exact absurd hs (by decide)
  · exact m13_2_9_5
  · exact m13_2_9_6
  · exact m13_2_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_9_11
  · exact m13_2_9_12

end Misses
