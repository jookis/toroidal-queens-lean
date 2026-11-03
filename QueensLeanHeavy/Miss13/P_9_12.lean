import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [9, 12]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_9_12_0_2 : go 13 7 9 [9, 12, 0, 2] = true := by decide +kernel
theorem m13_9_12_0_3 : go 13 7 9 [9, 12, 0, 3] = true := by decide +kernel
theorem m13_9_12_0_4 : go 13 7 9 [9, 12, 0, 4] = true := by decide +kernel
theorem m13_9_12_0_5 : go 13 7 9 [9, 12, 0, 5] = true := by decide +kernel
theorem m13_9_12_0_7 : go 13 7 9 [9, 12, 0, 7] = true := by decide +kernel
theorem m13_9_12_0_8 : go 13 7 9 [9, 12, 0, 8] = true := by decide +kernel
theorem m13_9_12_0_11 : go 13 7 9 [9, 12, 0, 11] = true := by decide +kernel

theorem m13_9_12_0 : go 13 7 10 [9, 12, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_0_2
  · exact m13_9_12_0_3
  · exact m13_9_12_0_4
  · exact m13_9_12_0_5
  · exact absurd hs (by decide)
  · exact m13_9_12_0_7
  · exact m13_9_12_0_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_0_11
  · exact absurd hs (by decide)

theorem m13_9_12_1_3 : go 13 7 9 [9, 12, 1, 3] = true := by decide +kernel
theorem m13_9_12_1_4 : go 13 7 9 [9, 12, 1, 4] = true := by decide +kernel
theorem m13_9_12_1_5 : go 13 7 9 [9, 12, 1, 5] = true := by decide +kernel
theorem m13_9_12_1_7 : go 13 7 9 [9, 12, 1, 7] = true := by decide +kernel
theorem m13_9_12_1_8 : go 13 7 9 [9, 12, 1, 8] = true := by decide +kernel
theorem m13_9_12_1_11 : go 13 7 9 [9, 12, 1, 11] = true := by decide +kernel

theorem m13_9_12_1 : go 13 7 10 [9, 12, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_1_3
  · exact m13_9_12_1_4
  · exact m13_9_12_1_5
  · exact absurd hs (by decide)
  · exact m13_9_12_1_7
  · exact m13_9_12_1_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_1_11
  · exact absurd hs (by decide)

theorem m13_9_12_2_0 : go 13 7 9 [9, 12, 2, 0] = true := by decide +kernel
theorem m13_9_12_2_4 : go 13 7 9 [9, 12, 2, 4] = true := by decide +kernel
theorem m13_9_12_2_5 : go 13 7 9 [9, 12, 2, 5] = true := by decide +kernel
theorem m13_9_12_2_7 : go 13 7 9 [9, 12, 2, 7] = true := by decide +kernel
theorem m13_9_12_2_8 : go 13 7 9 [9, 12, 2, 8] = true := by decide +kernel
theorem m13_9_12_2_11 : go 13 7 9 [9, 12, 2, 11] = true := by decide +kernel

theorem m13_9_12_2 : go 13 7 10 [9, 12, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_2_4
  · exact m13_9_12_2_5
  · exact absurd hs (by decide)
  · exact m13_9_12_2_7
  · exact m13_9_12_2_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_2_11
  · exact absurd hs (by decide)

theorem m13_9_12_3_0 : go 13 7 9 [9, 12, 3, 0] = true := by decide +kernel
theorem m13_9_12_3_1 : go 13 7 9 [9, 12, 3, 1] = true := by decide +kernel
theorem m13_9_12_3_5 : go 13 7 9 [9, 12, 3, 5] = true := by decide +kernel
theorem m13_9_12_3_7 : go 13 7 9 [9, 12, 3, 7] = true := by decide +kernel
theorem m13_9_12_3_8 : go 13 7 9 [9, 12, 3, 8] = true := by decide +kernel
theorem m13_9_12_3_11 : go 13 7 9 [9, 12, 3, 11] = true := by decide +kernel

theorem m13_9_12_3 : go 13 7 10 [9, 12, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_3_0
  · exact m13_9_12_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_3_5
  · exact absurd hs (by decide)
  · exact m13_9_12_3_7
  · exact m13_9_12_3_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_3_11
  · exact absurd hs (by decide)

theorem m13_9_12_4_0 : go 13 7 9 [9, 12, 4, 0] = true := by decide +kernel
theorem m13_9_12_4_1 : go 13 7 9 [9, 12, 4, 1] = true := by decide +kernel
theorem m13_9_12_4_2 : go 13 7 9 [9, 12, 4, 2] = true := by decide +kernel
theorem m13_9_12_4_7 : go 13 7 9 [9, 12, 4, 7] = true := by decide +kernel
theorem m13_9_12_4_8 : go 13 7 9 [9, 12, 4, 8] = true := by decide +kernel
theorem m13_9_12_4_11 : go 13 7 9 [9, 12, 4, 11] = true := by decide +kernel

theorem m13_9_12_4 : go 13 7 10 [9, 12, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_4_0
  · exact m13_9_12_4_1
  · exact m13_9_12_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_4_7
  · exact m13_9_12_4_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_4_11
  · exact absurd hs (by decide)

theorem m13_9_12_5_0 : go 13 7 9 [9, 12, 5, 0] = true := by decide +kernel
theorem m13_9_12_5_1 : go 13 7 9 [9, 12, 5, 1] = true := by decide +kernel
theorem m13_9_12_5_2 : go 13 7 9 [9, 12, 5, 2] = true := by decide +kernel
theorem m13_9_12_5_3 : go 13 7 9 [9, 12, 5, 3] = true := by decide +kernel
theorem m13_9_12_5_7 : go 13 7 9 [9, 12, 5, 7] = true := by decide +kernel
theorem m13_9_12_5_8 : go 13 7 9 [9, 12, 5, 8] = true := by decide +kernel
theorem m13_9_12_5_11 : go 13 7 9 [9, 12, 5, 11] = true := by decide +kernel

theorem m13_9_12_5 : go 13 7 10 [9, 12, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_5_0
  · exact m13_9_12_5_1
  · exact m13_9_12_5_2
  · exact m13_9_12_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_5_7
  · exact m13_9_12_5_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_5_11
  · exact absurd hs (by decide)

theorem m13_9_12_6_0 : go 13 7 9 [9, 12, 6, 0] = true := by decide +kernel
theorem m13_9_12_6_1 : go 13 7 9 [9, 12, 6, 1] = true := by decide +kernel
theorem m13_9_12_6_2 : go 13 7 9 [9, 12, 6, 2] = true := by decide +kernel
theorem m13_9_12_6_3 : go 13 7 9 [9, 12, 6, 3] = true := by decide +kernel
theorem m13_9_12_6_4 : go 13 7 9 [9, 12, 6, 4] = true := by decide +kernel
theorem m13_9_12_6_8 : go 13 7 9 [9, 12, 6, 8] = true := by decide +kernel
theorem m13_9_12_6_11 : go 13 7 9 [9, 12, 6, 11] = true := by decide +kernel

theorem m13_9_12_6 : go 13 7 10 [9, 12, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_6_0
  · exact m13_9_12_6_1
  · exact m13_9_12_6_2
  · exact m13_9_12_6_3
  · exact m13_9_12_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_6_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_6_11
  · exact absurd hs (by decide)

theorem m13_9_12_8_0 : go 13 7 9 [9, 12, 8, 0] = true := by decide +kernel
theorem m13_9_12_8_1 : go 13 7 9 [9, 12, 8, 1] = true := by decide +kernel
theorem m13_9_12_8_2 : go 13 7 9 [9, 12, 8, 2] = true := by decide +kernel
theorem m13_9_12_8_3 : go 13 7 9 [9, 12, 8, 3] = true := by decide +kernel
theorem m13_9_12_8_4 : go 13 7 9 [9, 12, 8, 4] = true := by decide +kernel
theorem m13_9_12_8_5 : go 13 7 9 [9, 12, 8, 5] = true := by decide +kernel
theorem m13_9_12_8_11 : go 13 7 9 [9, 12, 8, 11] = true := by decide +kernel

theorem m13_9_12_8 : go 13 7 10 [9, 12, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_8_0
  · exact m13_9_12_8_1
  · exact m13_9_12_8_2
  · exact m13_9_12_8_3
  · exact m13_9_12_8_4
  · exact m13_9_12_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_12_8_11
  · exact absurd hs (by decide)

theorem m13_9_12_10_0 : go 13 7 9 [9, 12, 10, 0] = true := by decide +kernel
theorem m13_9_12_10_1 : go 13 7 9 [9, 12, 10, 1] = true := by decide +kernel
theorem m13_9_12_10_2 : go 13 7 9 [9, 12, 10, 2] = true := by decide +kernel
theorem m13_9_12_10_3 : go 13 7 9 [9, 12, 10, 3] = true := by decide +kernel
theorem m13_9_12_10_4 : go 13 7 9 [9, 12, 10, 4] = true := by decide +kernel
theorem m13_9_12_10_5 : go 13 7 9 [9, 12, 10, 5] = true := by decide +kernel
theorem m13_9_12_10_7 : go 13 7 9 [9, 12, 10, 7] = true := by decide +kernel
theorem m13_9_12_10_8 : go 13 7 9 [9, 12, 10, 8] = true := by decide +kernel

theorem m13_9_12_10 : go 13 7 10 [9, 12, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_10_0
  · exact m13_9_12_10_1
  · exact m13_9_12_10_2
  · exact m13_9_12_10_3
  · exact m13_9_12_10_4
  · exact m13_9_12_10_5
  · exact absurd hs (by decide)
  · exact m13_9_12_10_7
  · exact m13_9_12_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_12 : go 13 7 11 [9, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_12_0
  · exact m13_9_12_1
  · exact m13_9_12_2
  · exact m13_9_12_3
  · exact m13_9_12_4
  · exact m13_9_12_5
  · exact m13_9_12_6
  · exact absurd hs (by decide)
  · exact m13_9_12_8
  · exact absurd hs (by decide)
  · exact m13_9_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
