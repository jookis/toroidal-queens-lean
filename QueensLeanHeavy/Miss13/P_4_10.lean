import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [4, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_4_10_0_2 : go 13 7 9 [4, 10, 0, 2] = true := by decide +kernel
theorem m13_4_10_0_3 : go 13 7 9 [4, 10, 0, 3] = true := by decide +kernel
theorem m13_4_10_0_5 : go 13 7 9 [4, 10, 0, 5] = true := by decide +kernel
theorem m13_4_10_0_6 : go 13 7 9 [4, 10, 0, 6] = true := by decide +kernel
theorem m13_4_10_0_9 : go 13 7 9 [4, 10, 0, 9] = true := by decide +kernel
theorem m13_4_10_0_11 : go 13 7 9 [4, 10, 0, 11] = true := by decide +kernel

theorem m13_4_10_0 : go 13 7 10 [4, 10, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_0_2
  · exact m13_4_10_0_3
  · exact absurd hs (by decide)
  · exact m13_4_10_0_5
  · exact m13_4_10_0_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_0_9
  · exact absurd hs (by decide)
  · exact m13_4_10_0_11
  · exact absurd hs (by decide)

theorem m13_4_10_1_3 : go 13 7 9 [4, 10, 1, 3] = true := by decide +kernel
theorem m13_4_10_1_5 : go 13 7 9 [4, 10, 1, 5] = true := by decide +kernel
theorem m13_4_10_1_6 : go 13 7 9 [4, 10, 1, 6] = true := by decide +kernel
theorem m13_4_10_1_9 : go 13 7 9 [4, 10, 1, 9] = true := by decide +kernel
theorem m13_4_10_1_11 : go 13 7 9 [4, 10, 1, 11] = true := by decide +kernel

theorem m13_4_10_1 : go 13 7 10 [4, 10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_1_3
  · exact absurd hs (by decide)
  · exact m13_4_10_1_5
  · exact m13_4_10_1_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_1_9
  · exact absurd hs (by decide)
  · exact m13_4_10_1_11
  · exact absurd hs (by decide)

theorem m13_4_10_3_0 : go 13 7 9 [4, 10, 3, 0] = true := by decide +kernel
theorem m13_4_10_3_5 : go 13 7 9 [4, 10, 3, 5] = true := by decide +kernel
theorem m13_4_10_3_6 : go 13 7 9 [4, 10, 3, 6] = true := by decide +kernel
theorem m13_4_10_3_9 : go 13 7 9 [4, 10, 3, 9] = true := by decide +kernel
theorem m13_4_10_3_11 : go 13 7 9 [4, 10, 3, 11] = true := by decide +kernel

theorem m13_4_10_3 : go 13 7 10 [4, 10, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_10_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_3_5
  · exact m13_4_10_3_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_3_9
  · exact absurd hs (by decide)
  · exact m13_4_10_3_11
  · exact absurd hs (by decide)

theorem m13_4_10_5_0 : go 13 7 9 [4, 10, 5, 0] = true := by decide +kernel
theorem m13_4_10_5_2 : go 13 7 9 [4, 10, 5, 2] = true := by decide +kernel
theorem m13_4_10_5_3 : go 13 7 9 [4, 10, 5, 3] = true := by decide +kernel
theorem m13_4_10_5_9 : go 13 7 9 [4, 10, 5, 9] = true := by decide +kernel
theorem m13_4_10_5_11 : go 13 7 9 [4, 10, 5, 11] = true := by decide +kernel

theorem m13_4_10_5 : go 13 7 10 [4, 10, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_10_5_0
  · exact absurd hs (by decide)
  · exact m13_4_10_5_2
  · exact m13_4_10_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_5_9
  · exact absurd hs (by decide)
  · exact m13_4_10_5_11
  · exact absurd hs (by decide)

theorem m13_4_10_7_0 : go 13 7 9 [4, 10, 7, 0] = true := by decide +kernel
theorem m13_4_10_7_2 : go 13 7 9 [4, 10, 7, 2] = true := by decide +kernel
theorem m13_4_10_7_3 : go 13 7 9 [4, 10, 7, 3] = true := by decide +kernel
theorem m13_4_10_7_5 : go 13 7 9 [4, 10, 7, 5] = true := by decide +kernel
theorem m13_4_10_7_9 : go 13 7 9 [4, 10, 7, 9] = true := by decide +kernel
theorem m13_4_10_7_11 : go 13 7 9 [4, 10, 7, 11] = true := by decide +kernel

theorem m13_4_10_7 : go 13 7 10 [4, 10, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_10_7_0
  · exact absurd hs (by decide)
  · exact m13_4_10_7_2
  · exact m13_4_10_7_3
  · exact absurd hs (by decide)
  · exact m13_4_10_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_7_9
  · exact absurd hs (by decide)
  · exact m13_4_10_7_11
  · exact absurd hs (by decide)

theorem m13_4_10_8_0 : go 13 7 9 [4, 10, 8, 0] = true := by decide +kernel
theorem m13_4_10_8_2 : go 13 7 9 [4, 10, 8, 2] = true := by decide +kernel
theorem m13_4_10_8_3 : go 13 7 9 [4, 10, 8, 3] = true := by decide +kernel
theorem m13_4_10_8_5 : go 13 7 9 [4, 10, 8, 5] = true := by decide +kernel
theorem m13_4_10_8_6 : go 13 7 9 [4, 10, 8, 6] = true := by decide +kernel
theorem m13_4_10_8_11 : go 13 7 9 [4, 10, 8, 11] = true := by decide +kernel

theorem m13_4_10_8 : go 13 7 10 [4, 10, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_10_8_0
  · exact absurd hs (by decide)
  · exact m13_4_10_8_2
  · exact m13_4_10_8_3
  · exact absurd hs (by decide)
  · exact m13_4_10_8_5
  · exact m13_4_10_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_8_11
  · exact absurd hs (by decide)

theorem m13_4_10_12_0 : go 13 7 9 [4, 10, 12, 0] = true := by decide +kernel
theorem m13_4_10_12_2 : go 13 7 9 [4, 10, 12, 2] = true := by decide +kernel
theorem m13_4_10_12_3 : go 13 7 9 [4, 10, 12, 3] = true := by decide +kernel
theorem m13_4_10_12_5 : go 13 7 9 [4, 10, 12, 5] = true := by decide +kernel
theorem m13_4_10_12_6 : go 13 7 9 [4, 10, 12, 6] = true := by decide +kernel
theorem m13_4_10_12_9 : go 13 7 9 [4, 10, 12, 9] = true := by decide +kernel

theorem m13_4_10_12 : go 13 7 10 [4, 10, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_10_12_0
  · exact absurd hs (by decide)
  · exact m13_4_10_12_2
  · exact m13_4_10_12_3
  · exact absurd hs (by decide)
  · exact m13_4_10_12_5
  · exact m13_4_10_12_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_10 : go 13 7 11 [4, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_10_0
  · exact m13_4_10_1
  · exact absurd hs (by decide)
  · exact m13_4_10_3
  · exact absurd hs (by decide)
  · exact m13_4_10_5
  · exact absurd hs (by decide)
  · exact m13_4_10_7
  · exact m13_4_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_10_12

end Misses
