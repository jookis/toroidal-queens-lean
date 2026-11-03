import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [1, 11]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_1_11_0_2 : go 13 7 9 [1, 11, 0, 2] = true := by decide +kernel
theorem m13_1_11_0_3 : go 13 7 9 [1, 11, 0, 3] = true := by decide +kernel
theorem m13_1_11_0_5 : go 13 7 9 [1, 11, 0, 5] = true := by decide +kernel
theorem m13_1_11_0_6 : go 13 7 9 [1, 11, 0, 6] = true := by decide +kernel
theorem m13_1_11_0_7 : go 13 7 9 [1, 11, 0, 7] = true := by decide +kernel
theorem m13_1_11_0_8 : go 13 7 9 [1, 11, 0, 8] = true := by decide +kernel
theorem m13_1_11_0_10 : go 13 7 9 [1, 11, 0, 10] = true := by decide +kernel
theorem m13_1_11_0_12 : go 13 7 9 [1, 11, 0, 12] = true := by decide +kernel

theorem m13_1_11_0 : go 13 7 10 [1, 11, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_0_2
  · exact m13_1_11_0_3
  · exact absurd hs (by decide)
  · exact m13_1_11_0_5
  · exact m13_1_11_0_6
  · exact m13_1_11_0_7
  · exact m13_1_11_0_8
  · exact absurd hs (by decide)
  · exact m13_1_11_0_10
  · exact absurd hs (by decide)
  · exact m13_1_11_0_12

theorem m13_1_11_2_0 : go 13 7 9 [1, 11, 2, 0] = true := by decide +kernel
theorem m13_1_11_2_5 : go 13 7 9 [1, 11, 2, 5] = true := by decide +kernel
theorem m13_1_11_2_6 : go 13 7 9 [1, 11, 2, 6] = true := by decide +kernel
theorem m13_1_11_2_7 : go 13 7 9 [1, 11, 2, 7] = true := by decide +kernel
theorem m13_1_11_2_8 : go 13 7 9 [1, 11, 2, 8] = true := by decide +kernel
theorem m13_1_11_2_10 : go 13 7 9 [1, 11, 2, 10] = true := by decide +kernel
theorem m13_1_11_2_12 : go 13 7 9 [1, 11, 2, 12] = true := by decide +kernel

theorem m13_1_11_2 : go 13 7 10 [1, 11, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_2_5
  · exact m13_1_11_2_6
  · exact m13_1_11_2_7
  · exact m13_1_11_2_8
  · exact absurd hs (by decide)
  · exact m13_1_11_2_10
  · exact absurd hs (by decide)
  · exact m13_1_11_2_12

theorem m13_1_11_4_0 : go 13 7 9 [1, 11, 4, 0] = true := by decide +kernel
theorem m13_1_11_4_2 : go 13 7 9 [1, 11, 4, 2] = true := by decide +kernel
theorem m13_1_11_4_6 : go 13 7 9 [1, 11, 4, 6] = true := by decide +kernel
theorem m13_1_11_4_7 : go 13 7 9 [1, 11, 4, 7] = true := by decide +kernel
theorem m13_1_11_4_8 : go 13 7 9 [1, 11, 4, 8] = true := by decide +kernel
theorem m13_1_11_4_10 : go 13 7 9 [1, 11, 4, 10] = true := by decide +kernel
theorem m13_1_11_4_12 : go 13 7 9 [1, 11, 4, 12] = true := by decide +kernel

theorem m13_1_11_4 : go 13 7 10 [1, 11, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_4_0
  · exact absurd hs (by decide)
  · exact m13_1_11_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_4_6
  · exact m13_1_11_4_7
  · exact m13_1_11_4_8
  · exact absurd hs (by decide)
  · exact m13_1_11_4_10
  · exact absurd hs (by decide)
  · exact m13_1_11_4_12

theorem m13_1_11_5_0 : go 13 7 9 [1, 11, 5, 0] = true := by decide +kernel
theorem m13_1_11_5_2 : go 13 7 9 [1, 11, 5, 2] = true := by decide +kernel
theorem m13_1_11_5_3 : go 13 7 9 [1, 11, 5, 3] = true := by decide +kernel
theorem m13_1_11_5_7 : go 13 7 9 [1, 11, 5, 7] = true := by decide +kernel
theorem m13_1_11_5_8 : go 13 7 9 [1, 11, 5, 8] = true := by decide +kernel
theorem m13_1_11_5_10 : go 13 7 9 [1, 11, 5, 10] = true := by decide +kernel
theorem m13_1_11_5_12 : go 13 7 9 [1, 11, 5, 12] = true := by decide +kernel

theorem m13_1_11_5 : go 13 7 10 [1, 11, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_5_0
  · exact absurd hs (by decide)
  · exact m13_1_11_5_2
  · exact m13_1_11_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_5_7
  · exact m13_1_11_5_8
  · exact absurd hs (by decide)
  · exact m13_1_11_5_10
  · exact absurd hs (by decide)
  · exact m13_1_11_5_12

theorem m13_1_11_6_0 : go 13 7 9 [1, 11, 6, 0] = true := by decide +kernel
theorem m13_1_11_6_2 : go 13 7 9 [1, 11, 6, 2] = true := by decide +kernel
theorem m13_1_11_6_3 : go 13 7 9 [1, 11, 6, 3] = true := by decide +kernel
theorem m13_1_11_6_8 : go 13 7 9 [1, 11, 6, 8] = true := by decide +kernel
theorem m13_1_11_6_10 : go 13 7 9 [1, 11, 6, 10] = true := by decide +kernel
theorem m13_1_11_6_12 : go 13 7 9 [1, 11, 6, 12] = true := by decide +kernel

theorem m13_1_11_6 : go 13 7 10 [1, 11, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_6_0
  · exact absurd hs (by decide)
  · exact m13_1_11_6_2
  · exact m13_1_11_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_6_8
  · exact absurd hs (by decide)
  · exact m13_1_11_6_10
  · exact absurd hs (by decide)
  · exact m13_1_11_6_12

theorem m13_1_11_7_0 : go 13 7 9 [1, 11, 7, 0] = true := by decide +kernel
theorem m13_1_11_7_2 : go 13 7 9 [1, 11, 7, 2] = true := by decide +kernel
theorem m13_1_11_7_3 : go 13 7 9 [1, 11, 7, 3] = true := by decide +kernel
theorem m13_1_11_7_5 : go 13 7 9 [1, 11, 7, 5] = true := by decide +kernel
theorem m13_1_11_7_10 : go 13 7 9 [1, 11, 7, 10] = true := by decide +kernel
theorem m13_1_11_7_12 : go 13 7 9 [1, 11, 7, 12] = true := by decide +kernel

theorem m13_1_11_7 : go 13 7 10 [1, 11, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_7_0
  · exact absurd hs (by decide)
  · exact m13_1_11_7_2
  · exact m13_1_11_7_3
  · exact absurd hs (by decide)
  · exact m13_1_11_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_7_10
  · exact absurd hs (by decide)
  · exact m13_1_11_7_12

theorem m13_1_11_8_0 : go 13 7 9 [1, 11, 8, 0] = true := by decide +kernel
theorem m13_1_11_8_2 : go 13 7 9 [1, 11, 8, 2] = true := by decide +kernel
theorem m13_1_11_8_3 : go 13 7 9 [1, 11, 8, 3] = true := by decide +kernel
theorem m13_1_11_8_5 : go 13 7 9 [1, 11, 8, 5] = true := by decide +kernel
theorem m13_1_11_8_6 : go 13 7 9 [1, 11, 8, 6] = true := by decide +kernel
theorem m13_1_11_8_10 : go 13 7 9 [1, 11, 8, 10] = true := by decide +kernel
theorem m13_1_11_8_12 : go 13 7 9 [1, 11, 8, 12] = true := by decide +kernel

theorem m13_1_11_8 : go 13 7 10 [1, 11, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_8_0
  · exact absurd hs (by decide)
  · exact m13_1_11_8_2
  · exact m13_1_11_8_3
  · exact absurd hs (by decide)
  · exact m13_1_11_8_5
  · exact m13_1_11_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_8_10
  · exact absurd hs (by decide)
  · exact m13_1_11_8_12

theorem m13_1_11_9_0 : go 13 7 9 [1, 11, 9, 0] = true := by decide +kernel
theorem m13_1_11_9_2 : go 13 7 9 [1, 11, 9, 2] = true := by decide +kernel
theorem m13_1_11_9_3 : go 13 7 9 [1, 11, 9, 3] = true := by decide +kernel
theorem m13_1_11_9_5 : go 13 7 9 [1, 11, 9, 5] = true := by decide +kernel
theorem m13_1_11_9_6 : go 13 7 9 [1, 11, 9, 6] = true := by decide +kernel
theorem m13_1_11_9_7 : go 13 7 9 [1, 11, 9, 7] = true := by decide +kernel
theorem m13_1_11_9_12 : go 13 7 9 [1, 11, 9, 12] = true := by decide +kernel

theorem m13_1_11_9 : go 13 7 10 [1, 11, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_9_0
  · exact absurd hs (by decide)
  · exact m13_1_11_9_2
  · exact m13_1_11_9_3
  · exact absurd hs (by decide)
  · exact m13_1_11_9_5
  · exact m13_1_11_9_6
  · exact m13_1_11_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_11_9_12

theorem m13_1_11 : go 13 7 11 [1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_11_0
  · exact absurd hs (by decide)
  · exact m13_1_11_2
  · exact absurd hs (by decide)
  · exact m13_1_11_4
  · exact m13_1_11_5
  · exact m13_1_11_6
  · exact m13_1_11_7
  · exact m13_1_11_8
  · exact m13_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
