import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [0, 7]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_0_7_1_4 : go 13 7 9 [0, 7, 1, 4] = true := by decide +kernel
theorem m13_0_7_1_6 : go 13 7 9 [0, 7, 1, 6] = true := by decide +kernel
theorem m13_0_7_1_8 : go 13 7 9 [0, 7, 1, 8] = true := by decide +kernel
theorem m13_0_7_1_10 : go 13 7 9 [0, 7, 1, 10] = true := by decide +kernel
theorem m13_0_7_1_11 : go 13 7 9 [0, 7, 1, 11] = true := by decide +kernel
theorem m13_0_7_1_12 : go 13 7 9 [0, 7, 1, 12] = true := by decide +kernel

theorem m13_0_7_1 : go 13 7 10 [0, 7, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_1_4
  · exact absurd hs (by decide)
  · exact m13_0_7_1_6
  · exact absurd hs (by decide)
  · exact m13_0_7_1_8
  · exact absurd hs (by decide)
  · exact m13_0_7_1_10
  · exact m13_0_7_1_11
  · exact m13_0_7_1_12

theorem m13_0_7_3_1 : go 13 7 9 [0, 7, 3, 1] = true := by decide +kernel
theorem m13_0_7_3_6 : go 13 7 9 [0, 7, 3, 6] = true := by decide +kernel
theorem m13_0_7_3_8 : go 13 7 9 [0, 7, 3, 8] = true := by decide +kernel
theorem m13_0_7_3_10 : go 13 7 9 [0, 7, 3, 10] = true := by decide +kernel
theorem m13_0_7_3_11 : go 13 7 9 [0, 7, 3, 11] = true := by decide +kernel
theorem m13_0_7_3_12 : go 13 7 9 [0, 7, 3, 12] = true := by decide +kernel

theorem m13_0_7_3 : go 13 7 10 [0, 7, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_3_6
  · exact absurd hs (by decide)
  · exact m13_0_7_3_8
  · exact absurd hs (by decide)
  · exact m13_0_7_3_10
  · exact m13_0_7_3_11
  · exact m13_0_7_3_12

theorem m13_0_7_4_1 : go 13 7 9 [0, 7, 4, 1] = true := by decide +kernel
theorem m13_0_7_4_2 : go 13 7 9 [0, 7, 4, 2] = true := by decide +kernel
theorem m13_0_7_4_6 : go 13 7 9 [0, 7, 4, 6] = true := by decide +kernel
theorem m13_0_7_4_8 : go 13 7 9 [0, 7, 4, 8] = true := by decide +kernel
theorem m13_0_7_4_10 : go 13 7 9 [0, 7, 4, 10] = true := by decide +kernel
theorem m13_0_7_4_11 : go 13 7 9 [0, 7, 4, 11] = true := by decide +kernel
theorem m13_0_7_4_12 : go 13 7 9 [0, 7, 4, 12] = true := by decide +kernel

theorem m13_0_7_4 : go 13 7 10 [0, 7, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_4_1
  · exact m13_0_7_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_4_6
  · exact absurd hs (by decide)
  · exact m13_0_7_4_8
  · exact absurd hs (by decide)
  · exact m13_0_7_4_10
  · exact m13_0_7_4_11
  · exact m13_0_7_4_12

theorem m13_0_7_5_1 : go 13 7 9 [0, 7, 5, 1] = true := by decide +kernel
theorem m13_0_7_5_2 : go 13 7 9 [0, 7, 5, 2] = true := by decide +kernel
theorem m13_0_7_5_8 : go 13 7 9 [0, 7, 5, 8] = true := by decide +kernel
theorem m13_0_7_5_10 : go 13 7 9 [0, 7, 5, 10] = true := by decide +kernel
theorem m13_0_7_5_11 : go 13 7 9 [0, 7, 5, 11] = true := by decide +kernel
theorem m13_0_7_5_12 : go 13 7 9 [0, 7, 5, 12] = true := by decide +kernel

theorem m13_0_7_5 : go 13 7 10 [0, 7, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_5_1
  · exact m13_0_7_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_5_8
  · exact absurd hs (by decide)
  · exact m13_0_7_5_10
  · exact m13_0_7_5_11
  · exact m13_0_7_5_12

theorem m13_0_7_9_1 : go 13 7 9 [0, 7, 9, 1] = true := by decide +kernel
theorem m13_0_7_9_2 : go 13 7 9 [0, 7, 9, 2] = true := by decide +kernel
theorem m13_0_7_9_4 : go 13 7 9 [0, 7, 9, 4] = true := by decide +kernel
theorem m13_0_7_9_6 : go 13 7 9 [0, 7, 9, 6] = true := by decide +kernel
theorem m13_0_7_9_11 : go 13 7 9 [0, 7, 9, 11] = true := by decide +kernel
theorem m13_0_7_9_12 : go 13 7 9 [0, 7, 9, 12] = true := by decide +kernel

theorem m13_0_7_9 : go 13 7 10 [0, 7, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_9_1
  · exact m13_0_7_9_2
  · exact absurd hs (by decide)
  · exact m13_0_7_9_4
  · exact absurd hs (by decide)
  · exact m13_0_7_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_9_11
  · exact m13_0_7_9_12

theorem m13_0_7_10_1 : go 13 7 9 [0, 7, 10, 1] = true := by decide +kernel
theorem m13_0_7_10_2 : go 13 7 9 [0, 7, 10, 2] = true := by decide +kernel
theorem m13_0_7_10_4 : go 13 7 9 [0, 7, 10, 4] = true := by decide +kernel
theorem m13_0_7_10_6 : go 13 7 9 [0, 7, 10, 6] = true := by decide +kernel
theorem m13_0_7_10_8 : go 13 7 9 [0, 7, 10, 8] = true := by decide +kernel
theorem m13_0_7_10_12 : go 13 7 9 [0, 7, 10, 12] = true := by decide +kernel

theorem m13_0_7_10 : go 13 7 10 [0, 7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_10_1
  · exact m13_0_7_10_2
  · exact absurd hs (by decide)
  · exact m13_0_7_10_4
  · exact absurd hs (by decide)
  · exact m13_0_7_10_6
  · exact absurd hs (by decide)
  · exact m13_0_7_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_10_12

theorem m13_0_7_11_1 : go 13 7 9 [0, 7, 11, 1] = true := by decide +kernel
theorem m13_0_7_11_2 : go 13 7 9 [0, 7, 11, 2] = true := by decide +kernel
theorem m13_0_7_11_4 : go 13 7 9 [0, 7, 11, 4] = true := by decide +kernel
theorem m13_0_7_11_6 : go 13 7 9 [0, 7, 11, 6] = true := by decide +kernel
theorem m13_0_7_11_8 : go 13 7 9 [0, 7, 11, 8] = true := by decide +kernel

theorem m13_0_7_11 : go 13 7 10 [0, 7, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_11_1
  · exact m13_0_7_11_2
  · exact absurd hs (by decide)
  · exact m13_0_7_11_4
  · exact absurd hs (by decide)
  · exact m13_0_7_11_6
  · exact absurd hs (by decide)
  · exact m13_0_7_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_0_7_12_1 : go 13 7 9 [0, 7, 12, 1] = true := by decide +kernel
theorem m13_0_7_12_2 : go 13 7 9 [0, 7, 12, 2] = true := by decide +kernel
theorem m13_0_7_12_4 : go 13 7 9 [0, 7, 12, 4] = true := by decide +kernel
theorem m13_0_7_12_6 : go 13 7 9 [0, 7, 12, 6] = true := by decide +kernel
theorem m13_0_7_12_8 : go 13 7 9 [0, 7, 12, 8] = true := by decide +kernel
theorem m13_0_7_12_10 : go 13 7 9 [0, 7, 12, 10] = true := by decide +kernel

theorem m13_0_7_12 : go 13 7 10 [0, 7, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_12_1
  · exact m13_0_7_12_2
  · exact absurd hs (by decide)
  · exact m13_0_7_12_4
  · exact absurd hs (by decide)
  · exact m13_0_7_12_6
  · exact absurd hs (by decide)
  · exact m13_0_7_12_8
  · exact absurd hs (by decide)
  · exact m13_0_7_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_0_7 : go 13 7 11 [0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_7_1
  · exact absurd hs (by decide)
  · exact m13_0_7_3
  · exact m13_0_7_4
  · exact m13_0_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_7_9
  · exact m13_0_7_10
  · exact m13_0_7_11
  · exact m13_0_7_12

end Misses
