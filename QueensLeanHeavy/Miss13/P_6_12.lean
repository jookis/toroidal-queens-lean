import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [6, 12]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_6_12_0_2 : go 13 7 9 [6, 12, 0, 2] = true := by decide +kernel
theorem m13_6_12_0_4 : go 13 7 9 [6, 12, 0, 4] = true := by decide +kernel
theorem m13_6_12_0_5 : go 13 7 9 [6, 12, 0, 5] = true := by decide +kernel
theorem m13_6_12_0_7 : go 13 7 9 [6, 12, 0, 7] = true := by decide +kernel
theorem m13_6_12_0_8 : go 13 7 9 [6, 12, 0, 8] = true := by decide +kernel
theorem m13_6_12_0_11 : go 13 7 9 [6, 12, 0, 11] = true := by decide +kernel

theorem m13_6_12_0 : go 13 7 10 [6, 12, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_0_2
  · exact absurd hs (by decide)
  · exact m13_6_12_0_4
  · exact m13_6_12_0_5
  · exact absurd hs (by decide)
  · exact m13_6_12_0_7
  · exact m13_6_12_0_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_0_11
  · exact absurd hs (by decide)

theorem m13_6_12_1_4 : go 13 7 9 [6, 12, 1, 4] = true := by decide +kernel
theorem m13_6_12_1_5 : go 13 7 9 [6, 12, 1, 5] = true := by decide +kernel
theorem m13_6_12_1_7 : go 13 7 9 [6, 12, 1, 7] = true := by decide +kernel
theorem m13_6_12_1_8 : go 13 7 9 [6, 12, 1, 8] = true := by decide +kernel
theorem m13_6_12_1_11 : go 13 7 9 [6, 12, 1, 11] = true := by decide +kernel

theorem m13_6_12_1 : go 13 7 10 [6, 12, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_1_4
  · exact m13_6_12_1_5
  · exact absurd hs (by decide)
  · exact m13_6_12_1_7
  · exact m13_6_12_1_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_1_11
  · exact absurd hs (by decide)

theorem m13_6_12_2_0 : go 13 7 9 [6, 12, 2, 0] = true := by decide +kernel
theorem m13_6_12_2_4 : go 13 7 9 [6, 12, 2, 4] = true := by decide +kernel
theorem m13_6_12_2_5 : go 13 7 9 [6, 12, 2, 5] = true := by decide +kernel
theorem m13_6_12_2_7 : go 13 7 9 [6, 12, 2, 7] = true := by decide +kernel
theorem m13_6_12_2_8 : go 13 7 9 [6, 12, 2, 8] = true := by decide +kernel
theorem m13_6_12_2_11 : go 13 7 9 [6, 12, 2, 11] = true := by decide +kernel

theorem m13_6_12_2 : go 13 7 10 [6, 12, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_2_4
  · exact m13_6_12_2_5
  · exact absurd hs (by decide)
  · exact m13_6_12_2_7
  · exact m13_6_12_2_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_2_11
  · exact absurd hs (by decide)

theorem m13_6_12_3_0 : go 13 7 9 [6, 12, 3, 0] = true := by decide +kernel
theorem m13_6_12_3_1 : go 13 7 9 [6, 12, 3, 1] = true := by decide +kernel
theorem m13_6_12_3_5 : go 13 7 9 [6, 12, 3, 5] = true := by decide +kernel
theorem m13_6_12_3_7 : go 13 7 9 [6, 12, 3, 7] = true := by decide +kernel
theorem m13_6_12_3_8 : go 13 7 9 [6, 12, 3, 8] = true := by decide +kernel
theorem m13_6_12_3_11 : go 13 7 9 [6, 12, 3, 11] = true := by decide +kernel

theorem m13_6_12_3 : go 13 7 10 [6, 12, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_3_0
  · exact m13_6_12_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_3_5
  · exact absurd hs (by decide)
  · exact m13_6_12_3_7
  · exact m13_6_12_3_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_3_11
  · exact absurd hs (by decide)

theorem m13_6_12_5_0 : go 13 7 9 [6, 12, 5, 0] = true := by decide +kernel
theorem m13_6_12_5_1 : go 13 7 9 [6, 12, 5, 1] = true := by decide +kernel
theorem m13_6_12_5_2 : go 13 7 9 [6, 12, 5, 2] = true := by decide +kernel
theorem m13_6_12_5_7 : go 13 7 9 [6, 12, 5, 7] = true := by decide +kernel
theorem m13_6_12_5_8 : go 13 7 9 [6, 12, 5, 8] = true := by decide +kernel
theorem m13_6_12_5_11 : go 13 7 9 [6, 12, 5, 11] = true := by decide +kernel

theorem m13_6_12_5 : go 13 7 10 [6, 12, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_5_0
  · exact m13_6_12_5_1
  · exact m13_6_12_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_5_7
  · exact m13_6_12_5_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_5_11
  · exact absurd hs (by decide)

theorem m13_6_12_7_0 : go 13 7 9 [6, 12, 7, 0] = true := by decide +kernel
theorem m13_6_12_7_1 : go 13 7 9 [6, 12, 7, 1] = true := by decide +kernel
theorem m13_6_12_7_2 : go 13 7 9 [6, 12, 7, 2] = true := by decide +kernel
theorem m13_6_12_7_4 : go 13 7 9 [6, 12, 7, 4] = true := by decide +kernel
theorem m13_6_12_7_5 : go 13 7 9 [6, 12, 7, 5] = true := by decide +kernel
theorem m13_6_12_7_11 : go 13 7 9 [6, 12, 7, 11] = true := by decide +kernel

theorem m13_6_12_7 : go 13 7 10 [6, 12, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_7_0
  · exact m13_6_12_7_1
  · exact m13_6_12_7_2
  · exact absurd hs (by decide)
  · exact m13_6_12_7_4
  · exact m13_6_12_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_7_11
  · exact absurd hs (by decide)

theorem m13_6_12_9_0 : go 13 7 9 [6, 12, 9, 0] = true := by decide +kernel
theorem m13_6_12_9_1 : go 13 7 9 [6, 12, 9, 1] = true := by decide +kernel
theorem m13_6_12_9_2 : go 13 7 9 [6, 12, 9, 2] = true := by decide +kernel
theorem m13_6_12_9_4 : go 13 7 9 [6, 12, 9, 4] = true := by decide +kernel
theorem m13_6_12_9_5 : go 13 7 9 [6, 12, 9, 5] = true := by decide +kernel
theorem m13_6_12_9_7 : go 13 7 9 [6, 12, 9, 7] = true := by decide +kernel
theorem m13_6_12_9_11 : go 13 7 9 [6, 12, 9, 11] = true := by decide +kernel

theorem m13_6_12_9 : go 13 7 10 [6, 12, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_9_0
  · exact m13_6_12_9_1
  · exact m13_6_12_9_2
  · exact absurd hs (by decide)
  · exact m13_6_12_9_4
  · exact m13_6_12_9_5
  · exact absurd hs (by decide)
  · exact m13_6_12_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_12_9_11
  · exact absurd hs (by decide)

theorem m13_6_12_10_0 : go 13 7 9 [6, 12, 10, 0] = true := by decide +kernel
theorem m13_6_12_10_1 : go 13 7 9 [6, 12, 10, 1] = true := by decide +kernel
theorem m13_6_12_10_2 : go 13 7 9 [6, 12, 10, 2] = true := by decide +kernel
theorem m13_6_12_10_4 : go 13 7 9 [6, 12, 10, 4] = true := by decide +kernel
theorem m13_6_12_10_5 : go 13 7 9 [6, 12, 10, 5] = true := by decide +kernel
theorem m13_6_12_10_7 : go 13 7 9 [6, 12, 10, 7] = true := by decide +kernel
theorem m13_6_12_10_8 : go 13 7 9 [6, 12, 10, 8] = true := by decide +kernel

theorem m13_6_12_10 : go 13 7 10 [6, 12, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_10_0
  · exact m13_6_12_10_1
  · exact m13_6_12_10_2
  · exact absurd hs (by decide)
  · exact m13_6_12_10_4
  · exact m13_6_12_10_5
  · exact absurd hs (by decide)
  · exact m13_6_12_10_7
  · exact m13_6_12_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_12 : go 13 7 11 [6, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_12_0
  · exact m13_6_12_1
  · exact m13_6_12_2
  · exact m13_6_12_3
  · exact absurd hs (by decide)
  · exact m13_6_12_5
  · exact absurd hs (by decide)
  · exact m13_6_12_7
  · exact absurd hs (by decide)
  · exact m13_6_12_9
  · exact m13_6_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
