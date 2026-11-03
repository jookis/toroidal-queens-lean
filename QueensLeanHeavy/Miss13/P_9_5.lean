import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [9, 5]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_9_5_0_2 : go 13 7 9 [9, 5, 0, 2] = true := by decide +kernel
theorem m13_9_5_0_4 : go 13 7 9 [9, 5, 0, 4] = true := by decide +kernel
theorem m13_9_5_0_8 : go 13 7 9 [9, 5, 0, 8] = true := by decide +kernel
theorem m13_9_5_0_10 : go 13 7 9 [9, 5, 0, 10] = true := by decide +kernel
theorem m13_9_5_0_11 : go 13 7 9 [9, 5, 0, 11] = true := by decide +kernel

theorem m13_9_5_0 : go 13 7 10 [9, 5, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_0_2
  · exact absurd hs (by decide)
  · exact m13_9_5_0_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_0_8
  · exact absurd hs (by decide)
  · exact m13_9_5_0_10
  · exact m13_9_5_0_11
  · exact absurd hs (by decide)

theorem m13_9_5_1_4 : go 13 7 9 [9, 5, 1, 4] = true := by decide +kernel
theorem m13_9_5_1_8 : go 13 7 9 [9, 5, 1, 8] = true := by decide +kernel
theorem m13_9_5_1_10 : go 13 7 9 [9, 5, 1, 10] = true := by decide +kernel
theorem m13_9_5_1_11 : go 13 7 9 [9, 5, 1, 11] = true := by decide +kernel

theorem m13_9_5_1 : go 13 7 10 [9, 5, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_1_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_1_8
  · exact absurd hs (by decide)
  · exact m13_9_5_1_10
  · exact m13_9_5_1_11
  · exact absurd hs (by decide)

theorem m13_9_5_2_0 : go 13 7 9 [9, 5, 2, 0] = true := by decide +kernel
theorem m13_9_5_2_4 : go 13 7 9 [9, 5, 2, 4] = true := by decide +kernel
theorem m13_9_5_2_8 : go 13 7 9 [9, 5, 2, 8] = true := by decide +kernel
theorem m13_9_5_2_10 : go 13 7 9 [9, 5, 2, 10] = true := by decide +kernel
theorem m13_9_5_2_11 : go 13 7 9 [9, 5, 2, 11] = true := by decide +kernel

theorem m13_9_5_2 : go 13 7 10 [9, 5, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_5_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_2_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_2_8
  · exact absurd hs (by decide)
  · exact m13_9_5_2_10
  · exact m13_9_5_2_11
  · exact absurd hs (by decide)

theorem m13_9_5_3_0 : go 13 7 9 [9, 5, 3, 0] = true := by decide +kernel
theorem m13_9_5_3_1 : go 13 7 9 [9, 5, 3, 1] = true := by decide +kernel
theorem m13_9_5_3_8 : go 13 7 9 [9, 5, 3, 8] = true := by decide +kernel
theorem m13_9_5_3_10 : go 13 7 9 [9, 5, 3, 10] = true := by decide +kernel
theorem m13_9_5_3_11 : go 13 7 9 [9, 5, 3, 11] = true := by decide +kernel

theorem m13_9_5_3 : go 13 7 10 [9, 5, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_5_3_0
  · exact m13_9_5_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_3_8
  · exact absurd hs (by decide)
  · exact m13_9_5_3_10
  · exact m13_9_5_3_11
  · exact absurd hs (by decide)

theorem m13_9_5_8_0 : go 13 7 9 [9, 5, 8, 0] = true := by decide +kernel
theorem m13_9_5_8_1 : go 13 7 9 [9, 5, 8, 1] = true := by decide +kernel
theorem m13_9_5_8_2 : go 13 7 9 [9, 5, 8, 2] = true := by decide +kernel
theorem m13_9_5_8_4 : go 13 7 9 [9, 5, 8, 4] = true := by decide +kernel
theorem m13_9_5_8_10 : go 13 7 9 [9, 5, 8, 10] = true := by decide +kernel
theorem m13_9_5_8_11 : go 13 7 9 [9, 5, 8, 11] = true := by decide +kernel

theorem m13_9_5_8 : go 13 7 10 [9, 5, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_5_8_0
  · exact m13_9_5_8_1
  · exact m13_9_5_8_2
  · exact absurd hs (by decide)
  · exact m13_9_5_8_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_8_10
  · exact m13_9_5_8_11
  · exact absurd hs (by decide)

theorem m13_9_5_10_0 : go 13 7 9 [9, 5, 10, 0] = true := by decide +kernel
theorem m13_9_5_10_1 : go 13 7 9 [9, 5, 10, 1] = true := by decide +kernel
theorem m13_9_5_10_2 : go 13 7 9 [9, 5, 10, 2] = true := by decide +kernel
theorem m13_9_5_10_4 : go 13 7 9 [9, 5, 10, 4] = true := by decide +kernel
theorem m13_9_5_10_8 : go 13 7 9 [9, 5, 10, 8] = true := by decide +kernel

theorem m13_9_5_10 : go 13 7 10 [9, 5, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_5_10_0
  · exact m13_9_5_10_1
  · exact m13_9_5_10_2
  · exact absurd hs (by decide)
  · exact m13_9_5_10_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_5_12_0 : go 13 7 9 [9, 5, 12, 0] = true := by decide +kernel
theorem m13_9_5_12_1 : go 13 7 9 [9, 5, 12, 1] = true := by decide +kernel
theorem m13_9_5_12_2 : go 13 7 9 [9, 5, 12, 2] = true := by decide +kernel
theorem m13_9_5_12_4 : go 13 7 9 [9, 5, 12, 4] = true := by decide +kernel
theorem m13_9_5_12_8 : go 13 7 9 [9, 5, 12, 8] = true := by decide +kernel
theorem m13_9_5_12_10 : go 13 7 9 [9, 5, 12, 10] = true := by decide +kernel

theorem m13_9_5_12 : go 13 7 10 [9, 5, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_5_12_0
  · exact m13_9_5_12_1
  · exact m13_9_5_12_2
  · exact absurd hs (by decide)
  · exact m13_9_5_12_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_12_8
  · exact absurd hs (by decide)
  · exact m13_9_5_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_5 : go 13 7 11 [9, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_5_0
  · exact m13_9_5_1
  · exact m13_9_5_2
  · exact m13_9_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_5_8
  · exact absurd hs (by decide)
  · exact m13_9_5_10
  · exact absurd hs (by decide)
  · exact m13_9_5_12

end Misses
