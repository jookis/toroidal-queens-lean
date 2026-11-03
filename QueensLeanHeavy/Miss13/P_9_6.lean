import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [9, 6]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_9_6_0_2 : go 13 7 9 [9, 6, 0, 2] = true := by decide +kernel
theorem m13_9_6_0_3 : go 13 7 9 [9, 6, 0, 3] = true := by decide +kernel
theorem m13_9_6_0_5 : go 13 7 9 [9, 6, 0, 5] = true := by decide +kernel
theorem m13_9_6_0_7 : go 13 7 9 [9, 6, 0, 7] = true := by decide +kernel
theorem m13_9_6_0_10 : go 13 7 9 [9, 6, 0, 10] = true := by decide +kernel
theorem m13_9_6_0_11 : go 13 7 9 [9, 6, 0, 11] = true := by decide +kernel

theorem m13_9_6_0 : go 13 7 10 [9, 6, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_0_2
  · exact m13_9_6_0_3
  · exact absurd hs (by decide)
  · exact m13_9_6_0_5
  · exact absurd hs (by decide)
  · exact m13_9_6_0_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_0_10
  · exact m13_9_6_0_11
  · exact absurd hs (by decide)

theorem m13_9_6_1_3 : go 13 7 9 [9, 6, 1, 3] = true := by decide +kernel
theorem m13_9_6_1_5 : go 13 7 9 [9, 6, 1, 5] = true := by decide +kernel
theorem m13_9_6_1_7 : go 13 7 9 [9, 6, 1, 7] = true := by decide +kernel
theorem m13_9_6_1_10 : go 13 7 9 [9, 6, 1, 10] = true := by decide +kernel
theorem m13_9_6_1_11 : go 13 7 9 [9, 6, 1, 11] = true := by decide +kernel

theorem m13_9_6_1 : go 13 7 10 [9, 6, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_1_3
  · exact absurd hs (by decide)
  · exact m13_9_6_1_5
  · exact absurd hs (by decide)
  · exact m13_9_6_1_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_1_10
  · exact m13_9_6_1_11
  · exact absurd hs (by decide)

theorem m13_9_6_2_0 : go 13 7 9 [9, 6, 2, 0] = true := by decide +kernel
theorem m13_9_6_2_5 : go 13 7 9 [9, 6, 2, 5] = true := by decide +kernel
theorem m13_9_6_2_7 : go 13 7 9 [9, 6, 2, 7] = true := by decide +kernel
theorem m13_9_6_2_10 : go 13 7 9 [9, 6, 2, 10] = true := by decide +kernel
theorem m13_9_6_2_11 : go 13 7 9 [9, 6, 2, 11] = true := by decide +kernel

theorem m13_9_6_2 : go 13 7 10 [9, 6, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_2_5
  · exact absurd hs (by decide)
  · exact m13_9_6_2_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_2_10
  · exact m13_9_6_2_11
  · exact absurd hs (by decide)

theorem m13_9_6_3_0 : go 13 7 9 [9, 6, 3, 0] = true := by decide +kernel
theorem m13_9_6_3_1 : go 13 7 9 [9, 6, 3, 1] = true := by decide +kernel
theorem m13_9_6_3_5 : go 13 7 9 [9, 6, 3, 5] = true := by decide +kernel
theorem m13_9_6_3_7 : go 13 7 9 [9, 6, 3, 7] = true := by decide +kernel
theorem m13_9_6_3_10 : go 13 7 9 [9, 6, 3, 10] = true := by decide +kernel
theorem m13_9_6_3_11 : go 13 7 9 [9, 6, 3, 11] = true := by decide +kernel

theorem m13_9_6_3 : go 13 7 10 [9, 6, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_3_0
  · exact m13_9_6_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_3_5
  · exact absurd hs (by decide)
  · exact m13_9_6_3_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_3_10
  · exact m13_9_6_3_11
  · exact absurd hs (by decide)

theorem m13_9_6_4_0 : go 13 7 9 [9, 6, 4, 0] = true := by decide +kernel
theorem m13_9_6_4_1 : go 13 7 9 [9, 6, 4, 1] = true := by decide +kernel
theorem m13_9_6_4_2 : go 13 7 9 [9, 6, 4, 2] = true := by decide +kernel
theorem m13_9_6_4_7 : go 13 7 9 [9, 6, 4, 7] = true := by decide +kernel
theorem m13_9_6_4_10 : go 13 7 9 [9, 6, 4, 10] = true := by decide +kernel
theorem m13_9_6_4_11 : go 13 7 9 [9, 6, 4, 11] = true := by decide +kernel

theorem m13_9_6_4 : go 13 7 10 [9, 6, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_4_0
  · exact m13_9_6_4_1
  · exact m13_9_6_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_4_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_4_10
  · exact m13_9_6_4_11
  · exact absurd hs (by decide)

theorem m13_9_6_8_0 : go 13 7 9 [9, 6, 8, 0] = true := by decide +kernel
theorem m13_9_6_8_1 : go 13 7 9 [9, 6, 8, 1] = true := by decide +kernel
theorem m13_9_6_8_2 : go 13 7 9 [9, 6, 8, 2] = true := by decide +kernel
theorem m13_9_6_8_3 : go 13 7 9 [9, 6, 8, 3] = true := by decide +kernel
theorem m13_9_6_8_5 : go 13 7 9 [9, 6, 8, 5] = true := by decide +kernel
theorem m13_9_6_8_10 : go 13 7 9 [9, 6, 8, 10] = true := by decide +kernel
theorem m13_9_6_8_11 : go 13 7 9 [9, 6, 8, 11] = true := by decide +kernel

theorem m13_9_6_8 : go 13 7 10 [9, 6, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_8_0
  · exact m13_9_6_8_1
  · exact m13_9_6_8_2
  · exact m13_9_6_8_3
  · exact absurd hs (by decide)
  · exact m13_9_6_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_8_10
  · exact m13_9_6_8_11
  · exact absurd hs (by decide)

theorem m13_9_6_10_0 : go 13 7 9 [9, 6, 10, 0] = true := by decide +kernel
theorem m13_9_6_10_1 : go 13 7 9 [9, 6, 10, 1] = true := by decide +kernel
theorem m13_9_6_10_2 : go 13 7 9 [9, 6, 10, 2] = true := by decide +kernel
theorem m13_9_6_10_3 : go 13 7 9 [9, 6, 10, 3] = true := by decide +kernel
theorem m13_9_6_10_5 : go 13 7 9 [9, 6, 10, 5] = true := by decide +kernel
theorem m13_9_6_10_7 : go 13 7 9 [9, 6, 10, 7] = true := by decide +kernel

theorem m13_9_6_10 : go 13 7 10 [9, 6, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_10_0
  · exact m13_9_6_10_1
  · exact m13_9_6_10_2
  · exact m13_9_6_10_3
  · exact absurd hs (by decide)
  · exact m13_9_6_10_5
  · exact absurd hs (by decide)
  · exact m13_9_6_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_6_12_0 : go 13 7 9 [9, 6, 12, 0] = true := by decide +kernel
theorem m13_9_6_12_1 : go 13 7 9 [9, 6, 12, 1] = true := by decide +kernel
theorem m13_9_6_12_2 : go 13 7 9 [9, 6, 12, 2] = true := by decide +kernel
theorem m13_9_6_12_3 : go 13 7 9 [9, 6, 12, 3] = true := by decide +kernel
theorem m13_9_6_12_5 : go 13 7 9 [9, 6, 12, 5] = true := by decide +kernel
theorem m13_9_6_12_7 : go 13 7 9 [9, 6, 12, 7] = true := by decide +kernel
theorem m13_9_6_12_10 : go 13 7 9 [9, 6, 12, 10] = true := by decide +kernel

theorem m13_9_6_12 : go 13 7 10 [9, 6, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_12_0
  · exact m13_9_6_12_1
  · exact m13_9_6_12_2
  · exact m13_9_6_12_3
  · exact absurd hs (by decide)
  · exact m13_9_6_12_5
  · exact absurd hs (by decide)
  · exact m13_9_6_12_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_6 : go 13 7 11 [9, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_6_0
  · exact m13_9_6_1
  · exact m13_9_6_2
  · exact m13_9_6_3
  · exact m13_9_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_6_8
  · exact absurd hs (by decide)
  · exact m13_9_6_10
  · exact absurd hs (by decide)
  · exact m13_9_6_12

end Misses
