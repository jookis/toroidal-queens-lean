import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [1, 9]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_1_9_0_2 : go 13 7 9 [1, 9, 0, 2] = true := by decide +kernel
theorem m13_1_9_0_3 : go 13 7 9 [1, 9, 0, 3] = true := by decide +kernel
theorem m13_1_9_0_5 : go 13 7 9 [1, 9, 0, 5] = true := by decide +kernel
theorem m13_1_9_0_6 : go 13 7 9 [1, 9, 0, 6] = true := by decide +kernel
theorem m13_1_9_0_8 : go 13 7 9 [1, 9, 0, 8] = true := by decide +kernel
theorem m13_1_9_0_10 : go 13 7 9 [1, 9, 0, 10] = true := by decide +kernel
theorem m13_1_9_0_12 : go 13 7 9 [1, 9, 0, 12] = true := by decide +kernel

theorem m13_1_9_0 : go 13 7 10 [1, 9, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_0_2
  · exact m13_1_9_0_3
  · exact absurd hs (by decide)
  · exact m13_1_9_0_5
  · exact m13_1_9_0_6
  · exact absurd hs (by decide)
  · exact m13_1_9_0_8
  · exact absurd hs (by decide)
  · exact m13_1_9_0_10
  · exact absurd hs (by decide)
  · exact m13_1_9_0_12

theorem m13_1_9_2_0 : go 13 7 9 [1, 9, 2, 0] = true := by decide +kernel
theorem m13_1_9_2_5 : go 13 7 9 [1, 9, 2, 5] = true := by decide +kernel
theorem m13_1_9_2_6 : go 13 7 9 [1, 9, 2, 6] = true := by decide +kernel
theorem m13_1_9_2_8 : go 13 7 9 [1, 9, 2, 8] = true := by decide +kernel
theorem m13_1_9_2_10 : go 13 7 9 [1, 9, 2, 10] = true := by decide +kernel
theorem m13_1_9_2_12 : go 13 7 9 [1, 9, 2, 12] = true := by decide +kernel

theorem m13_1_9_2 : go 13 7 10 [1, 9, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_2_5
  · exact m13_1_9_2_6
  · exact absurd hs (by decide)
  · exact m13_1_9_2_8
  · exact absurd hs (by decide)
  · exact m13_1_9_2_10
  · exact absurd hs (by decide)
  · exact m13_1_9_2_12

theorem m13_1_9_4_0 : go 13 7 9 [1, 9, 4, 0] = true := by decide +kernel
theorem m13_1_9_4_2 : go 13 7 9 [1, 9, 4, 2] = true := by decide +kernel
theorem m13_1_9_4_6 : go 13 7 9 [1, 9, 4, 6] = true := by decide +kernel
theorem m13_1_9_4_8 : go 13 7 9 [1, 9, 4, 8] = true := by decide +kernel
theorem m13_1_9_4_10 : go 13 7 9 [1, 9, 4, 10] = true := by decide +kernel
theorem m13_1_9_4_12 : go 13 7 9 [1, 9, 4, 12] = true := by decide +kernel

theorem m13_1_9_4 : go 13 7 10 [1, 9, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_4_0
  · exact absurd hs (by decide)
  · exact m13_1_9_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_4_6
  · exact absurd hs (by decide)
  · exact m13_1_9_4_8
  · exact absurd hs (by decide)
  · exact m13_1_9_4_10
  · exact absurd hs (by decide)
  · exact m13_1_9_4_12

theorem m13_1_9_5_0 : go 13 7 9 [1, 9, 5, 0] = true := by decide +kernel
theorem m13_1_9_5_2 : go 13 7 9 [1, 9, 5, 2] = true := by decide +kernel
theorem m13_1_9_5_3 : go 13 7 9 [1, 9, 5, 3] = true := by decide +kernel
theorem m13_1_9_5_8 : go 13 7 9 [1, 9, 5, 8] = true := by decide +kernel
theorem m13_1_9_5_10 : go 13 7 9 [1, 9, 5, 10] = true := by decide +kernel
theorem m13_1_9_5_12 : go 13 7 9 [1, 9, 5, 12] = true := by decide +kernel

theorem m13_1_9_5 : go 13 7 10 [1, 9, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_5_0
  · exact absurd hs (by decide)
  · exact m13_1_9_5_2
  · exact m13_1_9_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_5_8
  · exact absurd hs (by decide)
  · exact m13_1_9_5_10
  · exact absurd hs (by decide)
  · exact m13_1_9_5_12

theorem m13_1_9_6_0 : go 13 7 9 [1, 9, 6, 0] = true := by decide +kernel
theorem m13_1_9_6_2 : go 13 7 9 [1, 9, 6, 2] = true := by decide +kernel
theorem m13_1_9_6_3 : go 13 7 9 [1, 9, 6, 3] = true := by decide +kernel
theorem m13_1_9_6_8 : go 13 7 9 [1, 9, 6, 8] = true := by decide +kernel
theorem m13_1_9_6_10 : go 13 7 9 [1, 9, 6, 10] = true := by decide +kernel
theorem m13_1_9_6_12 : go 13 7 9 [1, 9, 6, 12] = true := by decide +kernel

theorem m13_1_9_6 : go 13 7 10 [1, 9, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_6_0
  · exact absurd hs (by decide)
  · exact m13_1_9_6_2
  · exact m13_1_9_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_6_8
  · exact absurd hs (by decide)
  · exact m13_1_9_6_10
  · exact absurd hs (by decide)
  · exact m13_1_9_6_12

theorem m13_1_9_7_0 : go 13 7 9 [1, 9, 7, 0] = true := by decide +kernel
theorem m13_1_9_7_2 : go 13 7 9 [1, 9, 7, 2] = true := by decide +kernel
theorem m13_1_9_7_3 : go 13 7 9 [1, 9, 7, 3] = true := by decide +kernel
theorem m13_1_9_7_5 : go 13 7 9 [1, 9, 7, 5] = true := by decide +kernel
theorem m13_1_9_7_10 : go 13 7 9 [1, 9, 7, 10] = true := by decide +kernel
theorem m13_1_9_7_12 : go 13 7 9 [1, 9, 7, 12] = true := by decide +kernel

theorem m13_1_9_7 : go 13 7 10 [1, 9, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_7_0
  · exact absurd hs (by decide)
  · exact m13_1_9_7_2
  · exact m13_1_9_7_3
  · exact absurd hs (by decide)
  · exact m13_1_9_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_7_10
  · exact absurd hs (by decide)
  · exact m13_1_9_7_12

theorem m13_1_9_11_0 : go 13 7 9 [1, 9, 11, 0] = true := by decide +kernel
theorem m13_1_9_11_2 : go 13 7 9 [1, 9, 11, 2] = true := by decide +kernel
theorem m13_1_9_11_3 : go 13 7 9 [1, 9, 11, 3] = true := by decide +kernel
theorem m13_1_9_11_5 : go 13 7 9 [1, 9, 11, 5] = true := by decide +kernel
theorem m13_1_9_11_6 : go 13 7 9 [1, 9, 11, 6] = true := by decide +kernel
theorem m13_1_9_11_8 : go 13 7 9 [1, 9, 11, 8] = true := by decide +kernel

theorem m13_1_9_11 : go 13 7 10 [1, 9, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_11_0
  · exact absurd hs (by decide)
  · exact m13_1_9_11_2
  · exact m13_1_9_11_3
  · exact absurd hs (by decide)
  · exact m13_1_9_11_5
  · exact m13_1_9_11_6
  · exact absurd hs (by decide)
  · exact m13_1_9_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_9_12_0 : go 13 7 9 [1, 9, 12, 0] = true := by decide +kernel
theorem m13_1_9_12_2 : go 13 7 9 [1, 9, 12, 2] = true := by decide +kernel
theorem m13_1_9_12_3 : go 13 7 9 [1, 9, 12, 3] = true := by decide +kernel
theorem m13_1_9_12_5 : go 13 7 9 [1, 9, 12, 5] = true := by decide +kernel
theorem m13_1_9_12_6 : go 13 7 9 [1, 9, 12, 6] = true := by decide +kernel
theorem m13_1_9_12_8 : go 13 7 9 [1, 9, 12, 8] = true := by decide +kernel
theorem m13_1_9_12_10 : go 13 7 9 [1, 9, 12, 10] = true := by decide +kernel

theorem m13_1_9_12 : go 13 7 10 [1, 9, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_12_0
  · exact absurd hs (by decide)
  · exact m13_1_9_12_2
  · exact m13_1_9_12_3
  · exact absurd hs (by decide)
  · exact m13_1_9_12_5
  · exact m13_1_9_12_6
  · exact absurd hs (by decide)
  · exact m13_1_9_12_8
  · exact absurd hs (by decide)
  · exact m13_1_9_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_9 : go 13 7 11 [1, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_9_0
  · exact absurd hs (by decide)
  · exact m13_1_9_2
  · exact absurd hs (by decide)
  · exact m13_1_9_4
  · exact m13_1_9_5
  · exact m13_1_9_6
  · exact m13_1_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_9_11
  · exact m13_1_9_12

end Misses
