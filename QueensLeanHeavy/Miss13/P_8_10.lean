import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [8, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_8_10_0_2 : go 13 7 9 [8, 10, 0, 2] = true := by decide +kernel
theorem m13_8_10_0_3 : go 13 7 9 [8, 10, 0, 3] = true := by decide +kernel
theorem m13_8_10_0_4 : go 13 7 9 [8, 10, 0, 4] = true := by decide +kernel
theorem m13_8_10_0_6 : go 13 7 9 [8, 10, 0, 6] = true := by decide +kernel
theorem m13_8_10_0_7 : go 13 7 9 [8, 10, 0, 7] = true := by decide +kernel
theorem m13_8_10_0_9 : go 13 7 9 [8, 10, 0, 9] = true := by decide +kernel

theorem m13_8_10_0 : go 13 7 10 [8, 10, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_0_2
  · exact m13_8_10_0_3
  · exact m13_8_10_0_4
  · exact absurd hs (by decide)
  · exact m13_8_10_0_6
  · exact m13_8_10_0_7
  · exact absurd hs (by decide)
  · exact m13_8_10_0_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_1_3 : go 13 7 9 [8, 10, 1, 3] = true := by decide +kernel
theorem m13_8_10_1_4 : go 13 7 9 [8, 10, 1, 4] = true := by decide +kernel
theorem m13_8_10_1_6 : go 13 7 9 [8, 10, 1, 6] = true := by decide +kernel
theorem m13_8_10_1_7 : go 13 7 9 [8, 10, 1, 7] = true := by decide +kernel
theorem m13_8_10_1_9 : go 13 7 9 [8, 10, 1, 9] = true := by decide +kernel

theorem m13_8_10_1 : go 13 7 10 [8, 10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_1_3
  · exact m13_8_10_1_4
  · exact absurd hs (by decide)
  · exact m13_8_10_1_6
  · exact m13_8_10_1_7
  · exact absurd hs (by decide)
  · exact m13_8_10_1_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_2_0 : go 13 7 9 [8, 10, 2, 0] = true := by decide +kernel
theorem m13_8_10_2_4 : go 13 7 9 [8, 10, 2, 4] = true := by decide +kernel
theorem m13_8_10_2_6 : go 13 7 9 [8, 10, 2, 6] = true := by decide +kernel
theorem m13_8_10_2_7 : go 13 7 9 [8, 10, 2, 7] = true := by decide +kernel
theorem m13_8_10_2_9 : go 13 7 9 [8, 10, 2, 9] = true := by decide +kernel

theorem m13_8_10_2 : go 13 7 10 [8, 10, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_2_4
  · exact absurd hs (by decide)
  · exact m13_8_10_2_6
  · exact m13_8_10_2_7
  · exact absurd hs (by decide)
  · exact m13_8_10_2_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_3_0 : go 13 7 9 [8, 10, 3, 0] = true := by decide +kernel
theorem m13_8_10_3_1 : go 13 7 9 [8, 10, 3, 1] = true := by decide +kernel
theorem m13_8_10_3_6 : go 13 7 9 [8, 10, 3, 6] = true := by decide +kernel
theorem m13_8_10_3_7 : go 13 7 9 [8, 10, 3, 7] = true := by decide +kernel
theorem m13_8_10_3_9 : go 13 7 9 [8, 10, 3, 9] = true := by decide +kernel

theorem m13_8_10_3 : go 13 7 10 [8, 10, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_3_0
  · exact m13_8_10_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_3_6
  · exact m13_8_10_3_7
  · exact absurd hs (by decide)
  · exact m13_8_10_3_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_4_0 : go 13 7 9 [8, 10, 4, 0] = true := by decide +kernel
theorem m13_8_10_4_1 : go 13 7 9 [8, 10, 4, 1] = true := by decide +kernel
theorem m13_8_10_4_2 : go 13 7 9 [8, 10, 4, 2] = true := by decide +kernel
theorem m13_8_10_4_6 : go 13 7 9 [8, 10, 4, 6] = true := by decide +kernel
theorem m13_8_10_4_7 : go 13 7 9 [8, 10, 4, 7] = true := by decide +kernel
theorem m13_8_10_4_9 : go 13 7 9 [8, 10, 4, 9] = true := by decide +kernel

theorem m13_8_10_4 : go 13 7 10 [8, 10, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_4_0
  · exact m13_8_10_4_1
  · exact m13_8_10_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_4_6
  · exact m13_8_10_4_7
  · exact absurd hs (by decide)
  · exact m13_8_10_4_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_5_0 : go 13 7 9 [8, 10, 5, 0] = true := by decide +kernel
theorem m13_8_10_5_1 : go 13 7 9 [8, 10, 5, 1] = true := by decide +kernel
theorem m13_8_10_5_2 : go 13 7 9 [8, 10, 5, 2] = true := by decide +kernel
theorem m13_8_10_5_3 : go 13 7 9 [8, 10, 5, 3] = true := by decide +kernel
theorem m13_8_10_5_7 : go 13 7 9 [8, 10, 5, 7] = true := by decide +kernel
theorem m13_8_10_5_9 : go 13 7 9 [8, 10, 5, 9] = true := by decide +kernel

theorem m13_8_10_5 : go 13 7 10 [8, 10, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_5_0
  · exact m13_8_10_5_1
  · exact m13_8_10_5_2
  · exact m13_8_10_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_5_7
  · exact absurd hs (by decide)
  · exact m13_8_10_5_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_7_0 : go 13 7 9 [8, 10, 7, 0] = true := by decide +kernel
theorem m13_8_10_7_1 : go 13 7 9 [8, 10, 7, 1] = true := by decide +kernel
theorem m13_8_10_7_2 : go 13 7 9 [8, 10, 7, 2] = true := by decide +kernel
theorem m13_8_10_7_3 : go 13 7 9 [8, 10, 7, 3] = true := by decide +kernel
theorem m13_8_10_7_4 : go 13 7 9 [8, 10, 7, 4] = true := by decide +kernel
theorem m13_8_10_7_9 : go 13 7 9 [8, 10, 7, 9] = true := by decide +kernel

theorem m13_8_10_7 : go 13 7 10 [8, 10, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_7_0
  · exact m13_8_10_7_1
  · exact m13_8_10_7_2
  · exact m13_8_10_7_3
  · exact m13_8_10_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_7_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10_12_0 : go 13 7 9 [8, 10, 12, 0] = true := by decide +kernel
theorem m13_8_10_12_1 : go 13 7 9 [8, 10, 12, 1] = true := by decide +kernel
theorem m13_8_10_12_2 : go 13 7 9 [8, 10, 12, 2] = true := by decide +kernel
theorem m13_8_10_12_3 : go 13 7 9 [8, 10, 12, 3] = true := by decide +kernel
theorem m13_8_10_12_4 : go 13 7 9 [8, 10, 12, 4] = true := by decide +kernel
theorem m13_8_10_12_6 : go 13 7 9 [8, 10, 12, 6] = true := by decide +kernel
theorem m13_8_10_12_7 : go 13 7 9 [8, 10, 12, 7] = true := by decide +kernel
theorem m13_8_10_12_9 : go 13 7 9 [8, 10, 12, 9] = true := by decide +kernel

theorem m13_8_10_12 : go 13 7 10 [8, 10, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_12_0
  · exact m13_8_10_12_1
  · exact m13_8_10_12_2
  · exact m13_8_10_12_3
  · exact m13_8_10_12_4
  · exact absurd hs (by decide)
  · exact m13_8_10_12_6
  · exact m13_8_10_12_7
  · exact absurd hs (by decide)
  · exact m13_8_10_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_10 : go 13 7 11 [8, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_10_0
  · exact m13_8_10_1
  · exact m13_8_10_2
  · exact m13_8_10_3
  · exact m13_8_10_4
  · exact m13_8_10_5
  · exact absurd hs (by decide)
  · exact m13_8_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_10_12

end Misses
