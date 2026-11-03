import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [7, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_7_10_0_2 : go 13 7 9 [7, 10, 0, 2] = true := by decide +kernel
theorem m13_7_10_0_3 : go 13 7 9 [7, 10, 0, 3] = true := by decide +kernel
theorem m13_7_10_0_5 : go 13 7 9 [7, 10, 0, 5] = true := by decide +kernel
theorem m13_7_10_0_6 : go 13 7 9 [7, 10, 0, 6] = true := by decide +kernel
theorem m13_7_10_0_9 : go 13 7 9 [7, 10, 0, 9] = true := by decide +kernel
theorem m13_7_10_0_11 : go 13 7 9 [7, 10, 0, 11] = true := by decide +kernel

theorem m13_7_10_0 : go 13 7 10 [7, 10, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_0_2
  · exact m13_7_10_0_3
  · exact absurd hs (by decide)
  · exact m13_7_10_0_5
  · exact m13_7_10_0_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_0_9
  · exact absurd hs (by decide)
  · exact m13_7_10_0_11
  · exact absurd hs (by decide)

theorem m13_7_10_1_3 : go 13 7 9 [7, 10, 1, 3] = true := by decide +kernel
theorem m13_7_10_1_5 : go 13 7 9 [7, 10, 1, 5] = true := by decide +kernel
theorem m13_7_10_1_6 : go 13 7 9 [7, 10, 1, 6] = true := by decide +kernel
theorem m13_7_10_1_9 : go 13 7 9 [7, 10, 1, 9] = true := by decide +kernel
theorem m13_7_10_1_11 : go 13 7 9 [7, 10, 1, 11] = true := by decide +kernel

theorem m13_7_10_1 : go 13 7 10 [7, 10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_1_3
  · exact absurd hs (by decide)
  · exact m13_7_10_1_5
  · exact m13_7_10_1_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_1_9
  · exact absurd hs (by decide)
  · exact m13_7_10_1_11
  · exact absurd hs (by decide)

theorem m13_7_10_2_0 : go 13 7 9 [7, 10, 2, 0] = true := by decide +kernel
theorem m13_7_10_2_5 : go 13 7 9 [7, 10, 2, 5] = true := by decide +kernel
theorem m13_7_10_2_6 : go 13 7 9 [7, 10, 2, 6] = true := by decide +kernel
theorem m13_7_10_2_9 : go 13 7 9 [7, 10, 2, 9] = true := by decide +kernel
theorem m13_7_10_2_11 : go 13 7 9 [7, 10, 2, 11] = true := by decide +kernel

theorem m13_7_10_2 : go 13 7 10 [7, 10, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_2_5
  · exact m13_7_10_2_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_2_9
  · exact absurd hs (by decide)
  · exact m13_7_10_2_11
  · exact absurd hs (by decide)

theorem m13_7_10_3_0 : go 13 7 9 [7, 10, 3, 0] = true := by decide +kernel
theorem m13_7_10_3_1 : go 13 7 9 [7, 10, 3, 1] = true := by decide +kernel
theorem m13_7_10_3_5 : go 13 7 9 [7, 10, 3, 5] = true := by decide +kernel
theorem m13_7_10_3_6 : go 13 7 9 [7, 10, 3, 6] = true := by decide +kernel
theorem m13_7_10_3_9 : go 13 7 9 [7, 10, 3, 9] = true := by decide +kernel
theorem m13_7_10_3_11 : go 13 7 9 [7, 10, 3, 11] = true := by decide +kernel

theorem m13_7_10_3 : go 13 7 10 [7, 10, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_3_0
  · exact m13_7_10_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_3_5
  · exact m13_7_10_3_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_3_9
  · exact absurd hs (by decide)
  · exact m13_7_10_3_11
  · exact absurd hs (by decide)

theorem m13_7_10_4_0 : go 13 7 9 [7, 10, 4, 0] = true := by decide +kernel
theorem m13_7_10_4_1 : go 13 7 9 [7, 10, 4, 1] = true := by decide +kernel
theorem m13_7_10_4_2 : go 13 7 9 [7, 10, 4, 2] = true := by decide +kernel
theorem m13_7_10_4_6 : go 13 7 9 [7, 10, 4, 6] = true := by decide +kernel
theorem m13_7_10_4_9 : go 13 7 9 [7, 10, 4, 9] = true := by decide +kernel
theorem m13_7_10_4_11 : go 13 7 9 [7, 10, 4, 11] = true := by decide +kernel

theorem m13_7_10_4 : go 13 7 10 [7, 10, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_4_0
  · exact m13_7_10_4_1
  · exact m13_7_10_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_4_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_4_9
  · exact absurd hs (by decide)
  · exact m13_7_10_4_11
  · exact absurd hs (by decide)

theorem m13_7_10_6_0 : go 13 7 9 [7, 10, 6, 0] = true := by decide +kernel
theorem m13_7_10_6_1 : go 13 7 9 [7, 10, 6, 1] = true := by decide +kernel
theorem m13_7_10_6_2 : go 13 7 9 [7, 10, 6, 2] = true := by decide +kernel
theorem m13_7_10_6_3 : go 13 7 9 [7, 10, 6, 3] = true := by decide +kernel
theorem m13_7_10_6_9 : go 13 7 9 [7, 10, 6, 9] = true := by decide +kernel
theorem m13_7_10_6_11 : go 13 7 9 [7, 10, 6, 11] = true := by decide +kernel

theorem m13_7_10_6 : go 13 7 10 [7, 10, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_6_0
  · exact m13_7_10_6_1
  · exact m13_7_10_6_2
  · exact m13_7_10_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_6_9
  · exact absurd hs (by decide)
  · exact m13_7_10_6_11
  · exact absurd hs (by decide)

theorem m13_7_10_8_0 : go 13 7 9 [7, 10, 8, 0] = true := by decide +kernel
theorem m13_7_10_8_1 : go 13 7 9 [7, 10, 8, 1] = true := by decide +kernel
theorem m13_7_10_8_2 : go 13 7 9 [7, 10, 8, 2] = true := by decide +kernel
theorem m13_7_10_8_3 : go 13 7 9 [7, 10, 8, 3] = true := by decide +kernel
theorem m13_7_10_8_5 : go 13 7 9 [7, 10, 8, 5] = true := by decide +kernel
theorem m13_7_10_8_6 : go 13 7 9 [7, 10, 8, 6] = true := by decide +kernel
theorem m13_7_10_8_11 : go 13 7 9 [7, 10, 8, 11] = true := by decide +kernel

theorem m13_7_10_8 : go 13 7 10 [7, 10, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_8_0
  · exact m13_7_10_8_1
  · exact m13_7_10_8_2
  · exact m13_7_10_8_3
  · exact absurd hs (by decide)
  · exact m13_7_10_8_5
  · exact m13_7_10_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_8_11
  · exact absurd hs (by decide)

theorem m13_7_10_12_0 : go 13 7 9 [7, 10, 12, 0] = true := by decide +kernel
theorem m13_7_10_12_1 : go 13 7 9 [7, 10, 12, 1] = true := by decide +kernel
theorem m13_7_10_12_2 : go 13 7 9 [7, 10, 12, 2] = true := by decide +kernel
theorem m13_7_10_12_3 : go 13 7 9 [7, 10, 12, 3] = true := by decide +kernel
theorem m13_7_10_12_5 : go 13 7 9 [7, 10, 12, 5] = true := by decide +kernel
theorem m13_7_10_12_6 : go 13 7 9 [7, 10, 12, 6] = true := by decide +kernel
theorem m13_7_10_12_9 : go 13 7 9 [7, 10, 12, 9] = true := by decide +kernel

theorem m13_7_10_12 : go 13 7 10 [7, 10, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_12_0
  · exact m13_7_10_12_1
  · exact m13_7_10_12_2
  · exact m13_7_10_12_3
  · exact absurd hs (by decide)
  · exact m13_7_10_12_5
  · exact m13_7_10_12_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_7_10 : go 13 7 11 [7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_10_0
  · exact m13_7_10_1
  · exact m13_7_10_2
  · exact m13_7_10_3
  · exact m13_7_10_4
  · exact absurd hs (by decide)
  · exact m13_7_10_6
  · exact absurd hs (by decide)
  · exact m13_7_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_10_12

end Misses
