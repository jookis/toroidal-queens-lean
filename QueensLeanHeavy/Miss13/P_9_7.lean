import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [9, 7]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_9_7_0_2 : go 13 7 9 [9, 7, 0, 2] = true := by decide +kernel
theorem m13_9_7_0_3 : go 13 7 9 [9, 7, 0, 3] = true := by decide +kernel
theorem m13_9_7_0_4 : go 13 7 9 [9, 7, 0, 4] = true := by decide +kernel
theorem m13_9_7_0_8 : go 13 7 9 [9, 7, 0, 8] = true := by decide +kernel
theorem m13_9_7_0_10 : go 13 7 9 [9, 7, 0, 10] = true := by decide +kernel
theorem m13_9_7_0_11 : go 13 7 9 [9, 7, 0, 11] = true := by decide +kernel

theorem m13_9_7_0 : go 13 7 10 [9, 7, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_0_2
  · exact m13_9_7_0_3
  · exact m13_9_7_0_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_0_8
  · exact absurd hs (by decide)
  · exact m13_9_7_0_10
  · exact m13_9_7_0_11
  · exact absurd hs (by decide)

theorem m13_9_7_1_3 : go 13 7 9 [9, 7, 1, 3] = true := by decide +kernel
theorem m13_9_7_1_4 : go 13 7 9 [9, 7, 1, 4] = true := by decide +kernel
theorem m13_9_7_1_8 : go 13 7 9 [9, 7, 1, 8] = true := by decide +kernel
theorem m13_9_7_1_10 : go 13 7 9 [9, 7, 1, 10] = true := by decide +kernel
theorem m13_9_7_1_11 : go 13 7 9 [9, 7, 1, 11] = true := by decide +kernel

theorem m13_9_7_1 : go 13 7 10 [9, 7, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_1_3
  · exact m13_9_7_1_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_1_8
  · exact absurd hs (by decide)
  · exact m13_9_7_1_10
  · exact m13_9_7_1_11
  · exact absurd hs (by decide)

theorem m13_9_7_2_0 : go 13 7 9 [9, 7, 2, 0] = true := by decide +kernel
theorem m13_9_7_2_4 : go 13 7 9 [9, 7, 2, 4] = true := by decide +kernel
theorem m13_9_7_2_8 : go 13 7 9 [9, 7, 2, 8] = true := by decide +kernel
theorem m13_9_7_2_10 : go 13 7 9 [9, 7, 2, 10] = true := by decide +kernel
theorem m13_9_7_2_11 : go 13 7 9 [9, 7, 2, 11] = true := by decide +kernel

theorem m13_9_7_2 : go 13 7 10 [9, 7, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_2_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_2_8
  · exact absurd hs (by decide)
  · exact m13_9_7_2_10
  · exact m13_9_7_2_11
  · exact absurd hs (by decide)

theorem m13_9_7_3_0 : go 13 7 9 [9, 7, 3, 0] = true := by decide +kernel
theorem m13_9_7_3_1 : go 13 7 9 [9, 7, 3, 1] = true := by decide +kernel
theorem m13_9_7_3_8 : go 13 7 9 [9, 7, 3, 8] = true := by decide +kernel
theorem m13_9_7_3_10 : go 13 7 9 [9, 7, 3, 10] = true := by decide +kernel
theorem m13_9_7_3_11 : go 13 7 9 [9, 7, 3, 11] = true := by decide +kernel

theorem m13_9_7_3 : go 13 7 10 [9, 7, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_3_0
  · exact m13_9_7_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_3_8
  · exact absurd hs (by decide)
  · exact m13_9_7_3_10
  · exact m13_9_7_3_11
  · exact absurd hs (by decide)

theorem m13_9_7_4_0 : go 13 7 9 [9, 7, 4, 0] = true := by decide +kernel
theorem m13_9_7_4_1 : go 13 7 9 [9, 7, 4, 1] = true := by decide +kernel
theorem m13_9_7_4_2 : go 13 7 9 [9, 7, 4, 2] = true := by decide +kernel
theorem m13_9_7_4_8 : go 13 7 9 [9, 7, 4, 8] = true := by decide +kernel
theorem m13_9_7_4_10 : go 13 7 9 [9, 7, 4, 10] = true := by decide +kernel
theorem m13_9_7_4_11 : go 13 7 9 [9, 7, 4, 11] = true := by decide +kernel

theorem m13_9_7_4 : go 13 7 10 [9, 7, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_4_0
  · exact m13_9_7_4_1
  · exact m13_9_7_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_4_8
  · exact absurd hs (by decide)
  · exact m13_9_7_4_10
  · exact m13_9_7_4_11
  · exact absurd hs (by decide)

theorem m13_9_7_5_0 : go 13 7 9 [9, 7, 5, 0] = true := by decide +kernel
theorem m13_9_7_5_1 : go 13 7 9 [9, 7, 5, 1] = true := by decide +kernel
theorem m13_9_7_5_2 : go 13 7 9 [9, 7, 5, 2] = true := by decide +kernel
theorem m13_9_7_5_3 : go 13 7 9 [9, 7, 5, 3] = true := by decide +kernel
theorem m13_9_7_5_8 : go 13 7 9 [9, 7, 5, 8] = true := by decide +kernel
theorem m13_9_7_5_10 : go 13 7 9 [9, 7, 5, 10] = true := by decide +kernel
theorem m13_9_7_5_11 : go 13 7 9 [9, 7, 5, 11] = true := by decide +kernel

theorem m13_9_7_5 : go 13 7 10 [9, 7, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_5_0
  · exact m13_9_7_5_1
  · exact m13_9_7_5_2
  · exact m13_9_7_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_5_8
  · exact absurd hs (by decide)
  · exact m13_9_7_5_10
  · exact m13_9_7_5_11
  · exact absurd hs (by decide)

theorem m13_9_7_10_0 : go 13 7 9 [9, 7, 10, 0] = true := by decide +kernel
theorem m13_9_7_10_1 : go 13 7 9 [9, 7, 10, 1] = true := by decide +kernel
theorem m13_9_7_10_2 : go 13 7 9 [9, 7, 10, 2] = true := by decide +kernel
theorem m13_9_7_10_3 : go 13 7 9 [9, 7, 10, 3] = true := by decide +kernel
theorem m13_9_7_10_4 : go 13 7 9 [9, 7, 10, 4] = true := by decide +kernel
theorem m13_9_7_10_8 : go 13 7 9 [9, 7, 10, 8] = true := by decide +kernel

theorem m13_9_7_10 : go 13 7 10 [9, 7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_10_0
  · exact m13_9_7_10_1
  · exact m13_9_7_10_2
  · exact m13_9_7_10_3
  · exact m13_9_7_10_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_7_12_0 : go 13 7 9 [9, 7, 12, 0] = true := by decide +kernel
theorem m13_9_7_12_1 : go 13 7 9 [9, 7, 12, 1] = true := by decide +kernel
theorem m13_9_7_12_2 : go 13 7 9 [9, 7, 12, 2] = true := by decide +kernel
theorem m13_9_7_12_3 : go 13 7 9 [9, 7, 12, 3] = true := by decide +kernel
theorem m13_9_7_12_4 : go 13 7 9 [9, 7, 12, 4] = true := by decide +kernel
theorem m13_9_7_12_8 : go 13 7 9 [9, 7, 12, 8] = true := by decide +kernel
theorem m13_9_7_12_10 : go 13 7 9 [9, 7, 12, 10] = true := by decide +kernel

theorem m13_9_7_12 : go 13 7 10 [9, 7, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_12_0
  · exact m13_9_7_12_1
  · exact m13_9_7_12_2
  · exact m13_9_7_12_3
  · exact m13_9_7_12_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_12_8
  · exact absurd hs (by decide)
  · exact m13_9_7_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_7 : go 13 7 11 [9, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_7_0
  · exact m13_9_7_1
  · exact m13_9_7_2
  · exact m13_9_7_3
  · exact m13_9_7_4
  · exact m13_9_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_7_10
  · exact absurd hs (by decide)
  · exact m13_9_7_12

end Misses
