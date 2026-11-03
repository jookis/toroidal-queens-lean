import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [10, 8]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_10_8_0_2 : go 13 7 9 [10, 8, 0, 2] = true := by decide +kernel
theorem m13_10_8_0_3 : go 13 7 9 [10, 8, 0, 3] = true := by decide +kernel
theorem m13_10_8_0_4 : go 13 7 9 [10, 8, 0, 4] = true := by decide +kernel
theorem m13_10_8_0_5 : go 13 7 9 [10, 8, 0, 5] = true := by decide +kernel
theorem m13_10_8_0_9 : go 13 7 9 [10, 8, 0, 9] = true := by decide +kernel
theorem m13_10_8_0_11 : go 13 7 9 [10, 8, 0, 11] = true := by decide +kernel
theorem m13_10_8_0_12 : go 13 7 9 [10, 8, 0, 12] = true := by decide +kernel

theorem m13_10_8_0 : go 13 7 10 [10, 8, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_0_2
  · exact m13_10_8_0_3
  · exact m13_10_8_0_4
  · exact m13_10_8_0_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_0_9
  · exact absurd hs (by decide)
  · exact m13_10_8_0_11
  · exact m13_10_8_0_12

theorem m13_10_8_1_3 : go 13 7 9 [10, 8, 1, 3] = true := by decide +kernel
theorem m13_10_8_1_4 : go 13 7 9 [10, 8, 1, 4] = true := by decide +kernel
theorem m13_10_8_1_5 : go 13 7 9 [10, 8, 1, 5] = true := by decide +kernel
theorem m13_10_8_1_9 : go 13 7 9 [10, 8, 1, 9] = true := by decide +kernel
theorem m13_10_8_1_11 : go 13 7 9 [10, 8, 1, 11] = true := by decide +kernel
theorem m13_10_8_1_12 : go 13 7 9 [10, 8, 1, 12] = true := by decide +kernel

theorem m13_10_8_1 : go 13 7 10 [10, 8, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_1_3
  · exact m13_10_8_1_4
  · exact m13_10_8_1_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_1_9
  · exact absurd hs (by decide)
  · exact m13_10_8_1_11
  · exact m13_10_8_1_12

theorem m13_10_8_2_0 : go 13 7 9 [10, 8, 2, 0] = true := by decide +kernel
theorem m13_10_8_2_4 : go 13 7 9 [10, 8, 2, 4] = true := by decide +kernel
theorem m13_10_8_2_5 : go 13 7 9 [10, 8, 2, 5] = true := by decide +kernel
theorem m13_10_8_2_9 : go 13 7 9 [10, 8, 2, 9] = true := by decide +kernel
theorem m13_10_8_2_11 : go 13 7 9 [10, 8, 2, 11] = true := by decide +kernel
theorem m13_10_8_2_12 : go 13 7 9 [10, 8, 2, 12] = true := by decide +kernel

theorem m13_10_8_2 : go 13 7 10 [10, 8, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_2_4
  · exact m13_10_8_2_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_2_9
  · exact absurd hs (by decide)
  · exact m13_10_8_2_11
  · exact m13_10_8_2_12

theorem m13_10_8_3_0 : go 13 7 9 [10, 8, 3, 0] = true := by decide +kernel
theorem m13_10_8_3_1 : go 13 7 9 [10, 8, 3, 1] = true := by decide +kernel
theorem m13_10_8_3_5 : go 13 7 9 [10, 8, 3, 5] = true := by decide +kernel
theorem m13_10_8_3_9 : go 13 7 9 [10, 8, 3, 9] = true := by decide +kernel
theorem m13_10_8_3_11 : go 13 7 9 [10, 8, 3, 11] = true := by decide +kernel
theorem m13_10_8_3_12 : go 13 7 9 [10, 8, 3, 12] = true := by decide +kernel

theorem m13_10_8_3 : go 13 7 10 [10, 8, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_3_0
  · exact m13_10_8_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_3_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_3_9
  · exact absurd hs (by decide)
  · exact m13_10_8_3_11
  · exact m13_10_8_3_12

theorem m13_10_8_4_0 : go 13 7 9 [10, 8, 4, 0] = true := by decide +kernel
theorem m13_10_8_4_1 : go 13 7 9 [10, 8, 4, 1] = true := by decide +kernel
theorem m13_10_8_4_2 : go 13 7 9 [10, 8, 4, 2] = true := by decide +kernel
theorem m13_10_8_4_9 : go 13 7 9 [10, 8, 4, 9] = true := by decide +kernel
theorem m13_10_8_4_11 : go 13 7 9 [10, 8, 4, 11] = true := by decide +kernel
theorem m13_10_8_4_12 : go 13 7 9 [10, 8, 4, 12] = true := by decide +kernel

theorem m13_10_8_4 : go 13 7 10 [10, 8, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_4_0
  · exact m13_10_8_4_1
  · exact m13_10_8_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_4_9
  · exact absurd hs (by decide)
  · exact m13_10_8_4_11
  · exact m13_10_8_4_12

theorem m13_10_8_5_0 : go 13 7 9 [10, 8, 5, 0] = true := by decide +kernel
theorem m13_10_8_5_1 : go 13 7 9 [10, 8, 5, 1] = true := by decide +kernel
theorem m13_10_8_5_2 : go 13 7 9 [10, 8, 5, 2] = true := by decide +kernel
theorem m13_10_8_5_3 : go 13 7 9 [10, 8, 5, 3] = true := by decide +kernel
theorem m13_10_8_5_9 : go 13 7 9 [10, 8, 5, 9] = true := by decide +kernel
theorem m13_10_8_5_11 : go 13 7 9 [10, 8, 5, 11] = true := by decide +kernel
theorem m13_10_8_5_12 : go 13 7 9 [10, 8, 5, 12] = true := by decide +kernel

theorem m13_10_8_5 : go 13 7 10 [10, 8, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_5_0
  · exact m13_10_8_5_1
  · exact m13_10_8_5_2
  · exact m13_10_8_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_5_9
  · exact absurd hs (by decide)
  · exact m13_10_8_5_11
  · exact m13_10_8_5_12

theorem m13_10_8_6_0 : go 13 7 9 [10, 8, 6, 0] = true := by decide +kernel
theorem m13_10_8_6_1 : go 13 7 9 [10, 8, 6, 1] = true := by decide +kernel
theorem m13_10_8_6_2 : go 13 7 9 [10, 8, 6, 2] = true := by decide +kernel
theorem m13_10_8_6_3 : go 13 7 9 [10, 8, 6, 3] = true := by decide +kernel
theorem m13_10_8_6_4 : go 13 7 9 [10, 8, 6, 4] = true := by decide +kernel
theorem m13_10_8_6_9 : go 13 7 9 [10, 8, 6, 9] = true := by decide +kernel
theorem m13_10_8_6_11 : go 13 7 9 [10, 8, 6, 11] = true := by decide +kernel
theorem m13_10_8_6_12 : go 13 7 9 [10, 8, 6, 12] = true := by decide +kernel

theorem m13_10_8_6 : go 13 7 10 [10, 8, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_6_0
  · exact m13_10_8_6_1
  · exact m13_10_8_6_2
  · exact m13_10_8_6_3
  · exact m13_10_8_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_6_9
  · exact absurd hs (by decide)
  · exact m13_10_8_6_11
  · exact m13_10_8_6_12

theorem m13_10_8_11_0 : go 13 7 9 [10, 8, 11, 0] = true := by decide +kernel
theorem m13_10_8_11_1 : go 13 7 9 [10, 8, 11, 1] = true := by decide +kernel
theorem m13_10_8_11_2 : go 13 7 9 [10, 8, 11, 2] = true := by decide +kernel
theorem m13_10_8_11_3 : go 13 7 9 [10, 8, 11, 3] = true := by decide +kernel
theorem m13_10_8_11_4 : go 13 7 9 [10, 8, 11, 4] = true := by decide +kernel
theorem m13_10_8_11_5 : go 13 7 9 [10, 8, 11, 5] = true := by decide +kernel
theorem m13_10_8_11_9 : go 13 7 9 [10, 8, 11, 9] = true := by decide +kernel

theorem m13_10_8_11 : go 13 7 10 [10, 8, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_11_0
  · exact m13_10_8_11_1
  · exact m13_10_8_11_2
  · exact m13_10_8_11_3
  · exact m13_10_8_11_4
  · exact m13_10_8_11_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_10_8 : go 13 7 11 [10, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_8_0
  · exact m13_10_8_1
  · exact m13_10_8_2
  · exact m13_10_8_3
  · exact m13_10_8_4
  · exact m13_10_8_5
  · exact m13_10_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_8_11
  · exact absurd hs (by decide)

end Misses
