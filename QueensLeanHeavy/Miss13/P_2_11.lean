import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 11]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_11_1_3 : go 13 7 9 [2, 11, 1, 3] = true := by decide +kernel
theorem m13_2_11_1_4 : go 13 7 9 [2, 11, 1, 4] = true := by decide +kernel
theorem m13_2_11_1_6 : go 13 7 9 [2, 11, 1, 6] = true := by decide +kernel
theorem m13_2_11_1_7 : go 13 7 9 [2, 11, 1, 7] = true := by decide +kernel
theorem m13_2_11_1_8 : go 13 7 9 [2, 11, 1, 8] = true := by decide +kernel
theorem m13_2_11_1_10 : go 13 7 9 [2, 11, 1, 10] = true := by decide +kernel
theorem m13_2_11_1_12 : go 13 7 9 [2, 11, 1, 12] = true := by decide +kernel

theorem m13_2_11_1 : go 13 7 10 [2, 11, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_1_3
  · exact m13_2_11_1_4
  · exact absurd hs (by decide)
  · exact m13_2_11_1_6
  · exact m13_2_11_1_7
  · exact m13_2_11_1_8
  · exact absurd hs (by decide)
  · exact m13_2_11_1_10
  · exact absurd hs (by decide)
  · exact m13_2_11_1_12

theorem m13_2_11_3_0 : go 13 7 9 [2, 11, 3, 0] = true := by decide +kernel
theorem m13_2_11_3_1 : go 13 7 9 [2, 11, 3, 1] = true := by decide +kernel
theorem m13_2_11_3_6 : go 13 7 9 [2, 11, 3, 6] = true := by decide +kernel
theorem m13_2_11_3_7 : go 13 7 9 [2, 11, 3, 7] = true := by decide +kernel
theorem m13_2_11_3_8 : go 13 7 9 [2, 11, 3, 8] = true := by decide +kernel
theorem m13_2_11_3_10 : go 13 7 9 [2, 11, 3, 10] = true := by decide +kernel
theorem m13_2_11_3_12 : go 13 7 9 [2, 11, 3, 12] = true := by decide +kernel

theorem m13_2_11_3 : go 13 7 10 [2, 11, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_11_3_0
  · exact m13_2_11_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_3_6
  · exact m13_2_11_3_7
  · exact m13_2_11_3_8
  · exact absurd hs (by decide)
  · exact m13_2_11_3_10
  · exact absurd hs (by decide)
  · exact m13_2_11_3_12

theorem m13_2_11_5_0 : go 13 7 9 [2, 11, 5, 0] = true := by decide +kernel
theorem m13_2_11_5_1 : go 13 7 9 [2, 11, 5, 1] = true := by decide +kernel
theorem m13_2_11_5_3 : go 13 7 9 [2, 11, 5, 3] = true := by decide +kernel
theorem m13_2_11_5_7 : go 13 7 9 [2, 11, 5, 7] = true := by decide +kernel
theorem m13_2_11_5_8 : go 13 7 9 [2, 11, 5, 8] = true := by decide +kernel
theorem m13_2_11_5_10 : go 13 7 9 [2, 11, 5, 10] = true := by decide +kernel
theorem m13_2_11_5_12 : go 13 7 9 [2, 11, 5, 12] = true := by decide +kernel

theorem m13_2_11_5 : go 13 7 10 [2, 11, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_11_5_0
  · exact m13_2_11_5_1
  · exact absurd hs (by decide)
  · exact m13_2_11_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_5_7
  · exact m13_2_11_5_8
  · exact absurd hs (by decide)
  · exact m13_2_11_5_10
  · exact absurd hs (by decide)
  · exact m13_2_11_5_12

theorem m13_2_11_6_0 : go 13 7 9 [2, 11, 6, 0] = true := by decide +kernel
theorem m13_2_11_6_1 : go 13 7 9 [2, 11, 6, 1] = true := by decide +kernel
theorem m13_2_11_6_3 : go 13 7 9 [2, 11, 6, 3] = true := by decide +kernel
theorem m13_2_11_6_4 : go 13 7 9 [2, 11, 6, 4] = true := by decide +kernel
theorem m13_2_11_6_8 : go 13 7 9 [2, 11, 6, 8] = true := by decide +kernel
theorem m13_2_11_6_10 : go 13 7 9 [2, 11, 6, 10] = true := by decide +kernel
theorem m13_2_11_6_12 : go 13 7 9 [2, 11, 6, 12] = true := by decide +kernel

theorem m13_2_11_6 : go 13 7 10 [2, 11, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_11_6_0
  · exact m13_2_11_6_1
  · exact absurd hs (by decide)
  · exact m13_2_11_6_3
  · exact m13_2_11_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_6_8
  · exact absurd hs (by decide)
  · exact m13_2_11_6_10
  · exact absurd hs (by decide)
  · exact m13_2_11_6_12

theorem m13_2_11_7_0 : go 13 7 9 [2, 11, 7, 0] = true := by decide +kernel
theorem m13_2_11_7_1 : go 13 7 9 [2, 11, 7, 1] = true := by decide +kernel
theorem m13_2_11_7_3 : go 13 7 9 [2, 11, 7, 3] = true := by decide +kernel
theorem m13_2_11_7_4 : go 13 7 9 [2, 11, 7, 4] = true := by decide +kernel
theorem m13_2_11_7_10 : go 13 7 9 [2, 11, 7, 10] = true := by decide +kernel
theorem m13_2_11_7_12 : go 13 7 9 [2, 11, 7, 12] = true := by decide +kernel

theorem m13_2_11_7 : go 13 7 10 [2, 11, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_11_7_0
  · exact m13_2_11_7_1
  · exact absurd hs (by decide)
  · exact m13_2_11_7_3
  · exact m13_2_11_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_7_10
  · exact absurd hs (by decide)
  · exact m13_2_11_7_12

theorem m13_2_11_8_0 : go 13 7 9 [2, 11, 8, 0] = true := by decide +kernel
theorem m13_2_11_8_1 : go 13 7 9 [2, 11, 8, 1] = true := by decide +kernel
theorem m13_2_11_8_3 : go 13 7 9 [2, 11, 8, 3] = true := by decide +kernel
theorem m13_2_11_8_4 : go 13 7 9 [2, 11, 8, 4] = true := by decide +kernel
theorem m13_2_11_8_6 : go 13 7 9 [2, 11, 8, 6] = true := by decide +kernel
theorem m13_2_11_8_10 : go 13 7 9 [2, 11, 8, 10] = true := by decide +kernel
theorem m13_2_11_8_12 : go 13 7 9 [2, 11, 8, 12] = true := by decide +kernel

theorem m13_2_11_8 : go 13 7 10 [2, 11, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_11_8_0
  · exact m13_2_11_8_1
  · exact absurd hs (by decide)
  · exact m13_2_11_8_3
  · exact m13_2_11_8_4
  · exact absurd hs (by decide)
  · exact m13_2_11_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_8_10
  · exact absurd hs (by decide)
  · exact m13_2_11_8_12

theorem m13_2_11_9_0 : go 13 7 9 [2, 11, 9, 0] = true := by decide +kernel
theorem m13_2_11_9_1 : go 13 7 9 [2, 11, 9, 1] = true := by decide +kernel
theorem m13_2_11_9_3 : go 13 7 9 [2, 11, 9, 3] = true := by decide +kernel
theorem m13_2_11_9_4 : go 13 7 9 [2, 11, 9, 4] = true := by decide +kernel
theorem m13_2_11_9_6 : go 13 7 9 [2, 11, 9, 6] = true := by decide +kernel
theorem m13_2_11_9_7 : go 13 7 9 [2, 11, 9, 7] = true := by decide +kernel
theorem m13_2_11_9_12 : go 13 7 9 [2, 11, 9, 12] = true := by decide +kernel

theorem m13_2_11_9 : go 13 7 10 [2, 11, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_11_9_0
  · exact m13_2_11_9_1
  · exact absurd hs (by decide)
  · exact m13_2_11_9_3
  · exact m13_2_11_9_4
  · exact absurd hs (by decide)
  · exact m13_2_11_9_6
  · exact m13_2_11_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_11_9_12

theorem m13_2_11 : go 13 7 11 [2, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_11_1
  · exact absurd hs (by decide)
  · exact m13_2_11_3
  · exact absurd hs (by decide)
  · exact m13_2_11_5
  · exact m13_2_11_6
  · exact m13_2_11_7
  · exact m13_2_11_8
  · exact m13_2_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
