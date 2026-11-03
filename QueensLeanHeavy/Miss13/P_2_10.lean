import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_10_1_3 : go 13 7 9 [2, 10, 1, 3] = true := by decide +kernel
theorem m13_2_10_1_4 : go 13 7 9 [2, 10, 1, 4] = true := by decide +kernel
theorem m13_2_10_1_6 : go 13 7 9 [2, 10, 1, 6] = true := by decide +kernel
theorem m13_2_10_1_7 : go 13 7 9 [2, 10, 1, 7] = true := by decide +kernel
theorem m13_2_10_1_9 : go 13 7 9 [2, 10, 1, 9] = true := by decide +kernel
theorem m13_2_10_1_11 : go 13 7 9 [2, 10, 1, 11] = true := by decide +kernel

theorem m13_2_10_1 : go 13 7 10 [2, 10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_1_3
  · exact m13_2_10_1_4
  · exact absurd hs (by decide)
  · exact m13_2_10_1_6
  · exact m13_2_10_1_7
  · exact absurd hs (by decide)
  · exact m13_2_10_1_9
  · exact absurd hs (by decide)
  · exact m13_2_10_1_11
  · exact absurd hs (by decide)

theorem m13_2_10_3_0 : go 13 7 9 [2, 10, 3, 0] = true := by decide +kernel
theorem m13_2_10_3_1 : go 13 7 9 [2, 10, 3, 1] = true := by decide +kernel
theorem m13_2_10_3_6 : go 13 7 9 [2, 10, 3, 6] = true := by decide +kernel
theorem m13_2_10_3_7 : go 13 7 9 [2, 10, 3, 7] = true := by decide +kernel
theorem m13_2_10_3_9 : go 13 7 9 [2, 10, 3, 9] = true := by decide +kernel
theorem m13_2_10_3_11 : go 13 7 9 [2, 10, 3, 11] = true := by decide +kernel

theorem m13_2_10_3 : go 13 7 10 [2, 10, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_10_3_0
  · exact m13_2_10_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_3_6
  · exact m13_2_10_3_7
  · exact absurd hs (by decide)
  · exact m13_2_10_3_9
  · exact absurd hs (by decide)
  · exact m13_2_10_3_11
  · exact absurd hs (by decide)

theorem m13_2_10_5_0 : go 13 7 9 [2, 10, 5, 0] = true := by decide +kernel
theorem m13_2_10_5_1 : go 13 7 9 [2, 10, 5, 1] = true := by decide +kernel
theorem m13_2_10_5_3 : go 13 7 9 [2, 10, 5, 3] = true := by decide +kernel
theorem m13_2_10_5_7 : go 13 7 9 [2, 10, 5, 7] = true := by decide +kernel
theorem m13_2_10_5_9 : go 13 7 9 [2, 10, 5, 9] = true := by decide +kernel
theorem m13_2_10_5_11 : go 13 7 9 [2, 10, 5, 11] = true := by decide +kernel

theorem m13_2_10_5 : go 13 7 10 [2, 10, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_10_5_0
  · exact m13_2_10_5_1
  · exact absurd hs (by decide)
  · exact m13_2_10_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_5_7
  · exact absurd hs (by decide)
  · exact m13_2_10_5_9
  · exact absurd hs (by decide)
  · exact m13_2_10_5_11
  · exact absurd hs (by decide)

theorem m13_2_10_6_0 : go 13 7 9 [2, 10, 6, 0] = true := by decide +kernel
theorem m13_2_10_6_1 : go 13 7 9 [2, 10, 6, 1] = true := by decide +kernel
theorem m13_2_10_6_3 : go 13 7 9 [2, 10, 6, 3] = true := by decide +kernel
theorem m13_2_10_6_4 : go 13 7 9 [2, 10, 6, 4] = true := by decide +kernel
theorem m13_2_10_6_9 : go 13 7 9 [2, 10, 6, 9] = true := by decide +kernel
theorem m13_2_10_6_11 : go 13 7 9 [2, 10, 6, 11] = true := by decide +kernel

theorem m13_2_10_6 : go 13 7 10 [2, 10, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_10_6_0
  · exact m13_2_10_6_1
  · exact absurd hs (by decide)
  · exact m13_2_10_6_3
  · exact m13_2_10_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_6_9
  · exact absurd hs (by decide)
  · exact m13_2_10_6_11
  · exact absurd hs (by decide)

theorem m13_2_10_7_0 : go 13 7 9 [2, 10, 7, 0] = true := by decide +kernel
theorem m13_2_10_7_1 : go 13 7 9 [2, 10, 7, 1] = true := by decide +kernel
theorem m13_2_10_7_3 : go 13 7 9 [2, 10, 7, 3] = true := by decide +kernel
theorem m13_2_10_7_4 : go 13 7 9 [2, 10, 7, 4] = true := by decide +kernel
theorem m13_2_10_7_9 : go 13 7 9 [2, 10, 7, 9] = true := by decide +kernel
theorem m13_2_10_7_11 : go 13 7 9 [2, 10, 7, 11] = true := by decide +kernel

theorem m13_2_10_7 : go 13 7 10 [2, 10, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_10_7_0
  · exact m13_2_10_7_1
  · exact absurd hs (by decide)
  · exact m13_2_10_7_3
  · exact m13_2_10_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_7_9
  · exact absurd hs (by decide)
  · exact m13_2_10_7_11
  · exact absurd hs (by decide)

theorem m13_2_10_8_0 : go 13 7 9 [2, 10, 8, 0] = true := by decide +kernel
theorem m13_2_10_8_1 : go 13 7 9 [2, 10, 8, 1] = true := by decide +kernel
theorem m13_2_10_8_3 : go 13 7 9 [2, 10, 8, 3] = true := by decide +kernel
theorem m13_2_10_8_4 : go 13 7 9 [2, 10, 8, 4] = true := by decide +kernel
theorem m13_2_10_8_6 : go 13 7 9 [2, 10, 8, 6] = true := by decide +kernel
theorem m13_2_10_8_11 : go 13 7 9 [2, 10, 8, 11] = true := by decide +kernel

theorem m13_2_10_8 : go 13 7 10 [2, 10, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_10_8_0
  · exact m13_2_10_8_1
  · exact absurd hs (by decide)
  · exact m13_2_10_8_3
  · exact m13_2_10_8_4
  · exact absurd hs (by decide)
  · exact m13_2_10_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_8_11
  · exact absurd hs (by decide)

theorem m13_2_10_12_0 : go 13 7 9 [2, 10, 12, 0] = true := by decide +kernel
theorem m13_2_10_12_1 : go 13 7 9 [2, 10, 12, 1] = true := by decide +kernel
theorem m13_2_10_12_3 : go 13 7 9 [2, 10, 12, 3] = true := by decide +kernel
theorem m13_2_10_12_4 : go 13 7 9 [2, 10, 12, 4] = true := by decide +kernel
theorem m13_2_10_12_6 : go 13 7 9 [2, 10, 12, 6] = true := by decide +kernel
theorem m13_2_10_12_7 : go 13 7 9 [2, 10, 12, 7] = true := by decide +kernel
theorem m13_2_10_12_9 : go 13 7 9 [2, 10, 12, 9] = true := by decide +kernel

theorem m13_2_10_12 : go 13 7 10 [2, 10, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_10_12_0
  · exact m13_2_10_12_1
  · exact absurd hs (by decide)
  · exact m13_2_10_12_3
  · exact m13_2_10_12_4
  · exact absurd hs (by decide)
  · exact m13_2_10_12_6
  · exact m13_2_10_12_7
  · exact absurd hs (by decide)
  · exact m13_2_10_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_10 : go 13 7 11 [2, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_10_1
  · exact absurd hs (by decide)
  · exact m13_2_10_3
  · exact absurd hs (by decide)
  · exact m13_2_10_5
  · exact m13_2_10_6
  · exact m13_2_10_7
  · exact m13_2_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_10_12

end Misses
