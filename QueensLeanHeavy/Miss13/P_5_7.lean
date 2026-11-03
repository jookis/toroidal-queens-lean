import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [5, 7]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_5_7_0_3 : go 13 7 9 [5, 7, 0, 3] = true := by decide +kernel
theorem m13_5_7_0_4 : go 13 7 9 [5, 7, 0, 4] = true := by decide +kernel
theorem m13_5_7_0_6 : go 13 7 9 [5, 7, 0, 6] = true := by decide +kernel
theorem m13_5_7_0_10 : go 13 7 9 [5, 7, 0, 10] = true := by decide +kernel
theorem m13_5_7_0_11 : go 13 7 9 [5, 7, 0, 11] = true := by decide +kernel
theorem m13_5_7_0_12 : go 13 7 9 [5, 7, 0, 12] = true := by decide +kernel

theorem m13_5_7_0 : go 13 7 10 [5, 7, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_0_3
  · exact m13_5_7_0_4
  · exact absurd hs (by decide)
  · exact m13_5_7_0_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_0_10
  · exact m13_5_7_0_11
  · exact m13_5_7_0_12

theorem m13_5_7_1_3 : go 13 7 9 [5, 7, 1, 3] = true := by decide +kernel
theorem m13_5_7_1_4 : go 13 7 9 [5, 7, 1, 4] = true := by decide +kernel
theorem m13_5_7_1_6 : go 13 7 9 [5, 7, 1, 6] = true := by decide +kernel
theorem m13_5_7_1_10 : go 13 7 9 [5, 7, 1, 10] = true := by decide +kernel
theorem m13_5_7_1_11 : go 13 7 9 [5, 7, 1, 11] = true := by decide +kernel
theorem m13_5_7_1_12 : go 13 7 9 [5, 7, 1, 12] = true := by decide +kernel

theorem m13_5_7_1 : go 13 7 10 [5, 7, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_1_3
  · exact m13_5_7_1_4
  · exact absurd hs (by decide)
  · exact m13_5_7_1_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_1_10
  · exact m13_5_7_1_11
  · exact m13_5_7_1_12

theorem m13_5_7_2_0 : go 13 7 9 [5, 7, 2, 0] = true := by decide +kernel
theorem m13_5_7_2_4 : go 13 7 9 [5, 7, 2, 4] = true := by decide +kernel
theorem m13_5_7_2_6 : go 13 7 9 [5, 7, 2, 6] = true := by decide +kernel
theorem m13_5_7_2_10 : go 13 7 9 [5, 7, 2, 10] = true := by decide +kernel
theorem m13_5_7_2_11 : go 13 7 9 [5, 7, 2, 11] = true := by decide +kernel
theorem m13_5_7_2_12 : go 13 7 9 [5, 7, 2, 12] = true := by decide +kernel

theorem m13_5_7_2 : go 13 7 10 [5, 7, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_2_4
  · exact absurd hs (by decide)
  · exact m13_5_7_2_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_2_10
  · exact m13_5_7_2_11
  · exact m13_5_7_2_12

theorem m13_5_7_4_0 : go 13 7 9 [5, 7, 4, 0] = true := by decide +kernel
theorem m13_5_7_4_1 : go 13 7 9 [5, 7, 4, 1] = true := by decide +kernel
theorem m13_5_7_4_6 : go 13 7 9 [5, 7, 4, 6] = true := by decide +kernel
theorem m13_5_7_4_10 : go 13 7 9 [5, 7, 4, 10] = true := by decide +kernel
theorem m13_5_7_4_11 : go 13 7 9 [5, 7, 4, 11] = true := by decide +kernel
theorem m13_5_7_4_12 : go 13 7 9 [5, 7, 4, 12] = true := by decide +kernel

theorem m13_5_7_4 : go 13 7 10 [5, 7, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_4_0
  · exact m13_5_7_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_4_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_4_10
  · exact m13_5_7_4_11
  · exact m13_5_7_4_12

theorem m13_5_7_9_0 : go 13 7 9 [5, 7, 9, 0] = true := by decide +kernel
theorem m13_5_7_9_1 : go 13 7 9 [5, 7, 9, 1] = true := by decide +kernel
theorem m13_5_7_9_3 : go 13 7 9 [5, 7, 9, 3] = true := by decide +kernel
theorem m13_5_7_9_4 : go 13 7 9 [5, 7, 9, 4] = true := by decide +kernel
theorem m13_5_7_9_6 : go 13 7 9 [5, 7, 9, 6] = true := by decide +kernel
theorem m13_5_7_9_11 : go 13 7 9 [5, 7, 9, 11] = true := by decide +kernel
theorem m13_5_7_9_12 : go 13 7 9 [5, 7, 9, 12] = true := by decide +kernel

theorem m13_5_7_9 : go 13 7 10 [5, 7, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_9_0
  · exact m13_5_7_9_1
  · exact absurd hs (by decide)
  · exact m13_5_7_9_3
  · exact m13_5_7_9_4
  · exact absurd hs (by decide)
  · exact m13_5_7_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_9_11
  · exact m13_5_7_9_12

theorem m13_5_7_10_0 : go 13 7 9 [5, 7, 10, 0] = true := by decide +kernel
theorem m13_5_7_10_1 : go 13 7 9 [5, 7, 10, 1] = true := by decide +kernel
theorem m13_5_7_10_3 : go 13 7 9 [5, 7, 10, 3] = true := by decide +kernel
theorem m13_5_7_10_4 : go 13 7 9 [5, 7, 10, 4] = true := by decide +kernel
theorem m13_5_7_10_6 : go 13 7 9 [5, 7, 10, 6] = true := by decide +kernel
theorem m13_5_7_10_12 : go 13 7 9 [5, 7, 10, 12] = true := by decide +kernel

theorem m13_5_7_10 : go 13 7 10 [5, 7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_10_0
  · exact m13_5_7_10_1
  · exact absurd hs (by decide)
  · exact m13_5_7_10_3
  · exact m13_5_7_10_4
  · exact absurd hs (by decide)
  · exact m13_5_7_10_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_10_12

theorem m13_5_7_11_0 : go 13 7 9 [5, 7, 11, 0] = true := by decide +kernel
theorem m13_5_7_11_1 : go 13 7 9 [5, 7, 11, 1] = true := by decide +kernel
theorem m13_5_7_11_3 : go 13 7 9 [5, 7, 11, 3] = true := by decide +kernel
theorem m13_5_7_11_4 : go 13 7 9 [5, 7, 11, 4] = true := by decide +kernel
theorem m13_5_7_11_6 : go 13 7 9 [5, 7, 11, 6] = true := by decide +kernel

theorem m13_5_7_11 : go 13 7 10 [5, 7, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_11_0
  · exact m13_5_7_11_1
  · exact absurd hs (by decide)
  · exact m13_5_7_11_3
  · exact m13_5_7_11_4
  · exact absurd hs (by decide)
  · exact m13_5_7_11_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_7_12_0 : go 13 7 9 [5, 7, 12, 0] = true := by decide +kernel
theorem m13_5_7_12_1 : go 13 7 9 [5, 7, 12, 1] = true := by decide +kernel
theorem m13_5_7_12_3 : go 13 7 9 [5, 7, 12, 3] = true := by decide +kernel
theorem m13_5_7_12_4 : go 13 7 9 [5, 7, 12, 4] = true := by decide +kernel
theorem m13_5_7_12_6 : go 13 7 9 [5, 7, 12, 6] = true := by decide +kernel
theorem m13_5_7_12_10 : go 13 7 9 [5, 7, 12, 10] = true := by decide +kernel

theorem m13_5_7_12 : go 13 7 10 [5, 7, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_12_0
  · exact m13_5_7_12_1
  · exact absurd hs (by decide)
  · exact m13_5_7_12_3
  · exact m13_5_7_12_4
  · exact absurd hs (by decide)
  · exact m13_5_7_12_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_7 : go 13 7 11 [5, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_7_0
  · exact m13_5_7_1
  · exact m13_5_7_2
  · exact absurd hs (by decide)
  · exact m13_5_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_7_9
  · exact m13_5_7_10
  · exact m13_5_7_11
  · exact m13_5_7_12

end Misses
