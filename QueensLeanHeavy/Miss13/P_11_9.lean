import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [11, 9]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_11_9_0_2 : go 13 7 9 [11, 9, 0, 2] = true := by decide +kernel
theorem m13_11_9_0_3 : go 13 7 9 [11, 9, 0, 3] = true := by decide +kernel
theorem m13_11_9_0_4 : go 13 7 9 [11, 9, 0, 4] = true := by decide +kernel
theorem m13_11_9_0_5 : go 13 7 9 [11, 9, 0, 5] = true := by decide +kernel
theorem m13_11_9_0_6 : go 13 7 9 [11, 9, 0, 6] = true := by decide +kernel
theorem m13_11_9_0_10 : go 13 7 9 [11, 9, 0, 10] = true := by decide +kernel
theorem m13_11_9_0_12 : go 13 7 9 [11, 9, 0, 12] = true := by decide +kernel

theorem m13_11_9_0 : go 13 7 10 [11, 9, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_0_2
  · exact m13_11_9_0_3
  · exact m13_11_9_0_4
  · exact m13_11_9_0_5
  · exact m13_11_9_0_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_0_10
  · exact absurd hs (by decide)
  · exact m13_11_9_0_12

theorem m13_11_9_1_3 : go 13 7 9 [11, 9, 1, 3] = true := by decide +kernel
theorem m13_11_9_1_4 : go 13 7 9 [11, 9, 1, 4] = true := by decide +kernel
theorem m13_11_9_1_5 : go 13 7 9 [11, 9, 1, 5] = true := by decide +kernel
theorem m13_11_9_1_6 : go 13 7 9 [11, 9, 1, 6] = true := by decide +kernel
theorem m13_11_9_1_10 : go 13 7 9 [11, 9, 1, 10] = true := by decide +kernel
theorem m13_11_9_1_12 : go 13 7 9 [11, 9, 1, 12] = true := by decide +kernel

theorem m13_11_9_1 : go 13 7 10 [11, 9, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_1_3
  · exact m13_11_9_1_4
  · exact m13_11_9_1_5
  · exact m13_11_9_1_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_1_10
  · exact absurd hs (by decide)
  · exact m13_11_9_1_12

theorem m13_11_9_2_0 : go 13 7 9 [11, 9, 2, 0] = true := by decide +kernel
theorem m13_11_9_2_4 : go 13 7 9 [11, 9, 2, 4] = true := by decide +kernel
theorem m13_11_9_2_5 : go 13 7 9 [11, 9, 2, 5] = true := by decide +kernel
theorem m13_11_9_2_6 : go 13 7 9 [11, 9, 2, 6] = true := by decide +kernel
theorem m13_11_9_2_10 : go 13 7 9 [11, 9, 2, 10] = true := by decide +kernel
theorem m13_11_9_2_12 : go 13 7 9 [11, 9, 2, 12] = true := by decide +kernel

theorem m13_11_9_2 : go 13 7 10 [11, 9, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_2_4
  · exact m13_11_9_2_5
  · exact m13_11_9_2_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_2_10
  · exact absurd hs (by decide)
  · exact m13_11_9_2_12

theorem m13_11_9_3_0 : go 13 7 9 [11, 9, 3, 0] = true := by decide +kernel
theorem m13_11_9_3_1 : go 13 7 9 [11, 9, 3, 1] = true := by decide +kernel
theorem m13_11_9_3_5 : go 13 7 9 [11, 9, 3, 5] = true := by decide +kernel
theorem m13_11_9_3_6 : go 13 7 9 [11, 9, 3, 6] = true := by decide +kernel
theorem m13_11_9_3_10 : go 13 7 9 [11, 9, 3, 10] = true := by decide +kernel
theorem m13_11_9_3_12 : go 13 7 9 [11, 9, 3, 12] = true := by decide +kernel

theorem m13_11_9_3 : go 13 7 10 [11, 9, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_3_0
  · exact m13_11_9_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_3_5
  · exact m13_11_9_3_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_3_10
  · exact absurd hs (by decide)
  · exact m13_11_9_3_12

theorem m13_11_9_4_0 : go 13 7 9 [11, 9, 4, 0] = true := by decide +kernel
theorem m13_11_9_4_1 : go 13 7 9 [11, 9, 4, 1] = true := by decide +kernel
theorem m13_11_9_4_2 : go 13 7 9 [11, 9, 4, 2] = true := by decide +kernel
theorem m13_11_9_4_6 : go 13 7 9 [11, 9, 4, 6] = true := by decide +kernel
theorem m13_11_9_4_10 : go 13 7 9 [11, 9, 4, 10] = true := by decide +kernel
theorem m13_11_9_4_12 : go 13 7 9 [11, 9, 4, 12] = true := by decide +kernel

theorem m13_11_9_4 : go 13 7 10 [11, 9, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_4_0
  · exact m13_11_9_4_1
  · exact m13_11_9_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_4_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_4_10
  · exact absurd hs (by decide)
  · exact m13_11_9_4_12

theorem m13_11_9_5_0 : go 13 7 9 [11, 9, 5, 0] = true := by decide +kernel
theorem m13_11_9_5_1 : go 13 7 9 [11, 9, 5, 1] = true := by decide +kernel
theorem m13_11_9_5_2 : go 13 7 9 [11, 9, 5, 2] = true := by decide +kernel
theorem m13_11_9_5_3 : go 13 7 9 [11, 9, 5, 3] = true := by decide +kernel
theorem m13_11_9_5_10 : go 13 7 9 [11, 9, 5, 10] = true := by decide +kernel
theorem m13_11_9_5_12 : go 13 7 9 [11, 9, 5, 12] = true := by decide +kernel

theorem m13_11_9_5 : go 13 7 10 [11, 9, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_5_0
  · exact m13_11_9_5_1
  · exact m13_11_9_5_2
  · exact m13_11_9_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_5_10
  · exact absurd hs (by decide)
  · exact m13_11_9_5_12

theorem m13_11_9_6_0 : go 13 7 9 [11, 9, 6, 0] = true := by decide +kernel
theorem m13_11_9_6_1 : go 13 7 9 [11, 9, 6, 1] = true := by decide +kernel
theorem m13_11_9_6_2 : go 13 7 9 [11, 9, 6, 2] = true := by decide +kernel
theorem m13_11_9_6_3 : go 13 7 9 [11, 9, 6, 3] = true := by decide +kernel
theorem m13_11_9_6_4 : go 13 7 9 [11, 9, 6, 4] = true := by decide +kernel
theorem m13_11_9_6_10 : go 13 7 9 [11, 9, 6, 10] = true := by decide +kernel
theorem m13_11_9_6_12 : go 13 7 9 [11, 9, 6, 12] = true := by decide +kernel

theorem m13_11_9_6 : go 13 7 10 [11, 9, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_6_0
  · exact m13_11_9_6_1
  · exact m13_11_9_6_2
  · exact m13_11_9_6_3
  · exact m13_11_9_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_6_10
  · exact absurd hs (by decide)
  · exact m13_11_9_6_12

theorem m13_11_9_7_0 : go 13 7 9 [11, 9, 7, 0] = true := by decide +kernel
theorem m13_11_9_7_1 : go 13 7 9 [11, 9, 7, 1] = true := by decide +kernel
theorem m13_11_9_7_2 : go 13 7 9 [11, 9, 7, 2] = true := by decide +kernel
theorem m13_11_9_7_3 : go 13 7 9 [11, 9, 7, 3] = true := by decide +kernel
theorem m13_11_9_7_4 : go 13 7 9 [11, 9, 7, 4] = true := by decide +kernel
theorem m13_11_9_7_5 : go 13 7 9 [11, 9, 7, 5] = true := by decide +kernel
theorem m13_11_9_7_10 : go 13 7 9 [11, 9, 7, 10] = true := by decide +kernel
theorem m13_11_9_7_12 : go 13 7 9 [11, 9, 7, 12] = true := by decide +kernel

theorem m13_11_9_7 : go 13 7 10 [11, 9, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_7_0
  · exact m13_11_9_7_1
  · exact m13_11_9_7_2
  · exact m13_11_9_7_3
  · exact m13_11_9_7_4
  · exact m13_11_9_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_7_10
  · exact absurd hs (by decide)
  · exact m13_11_9_7_12

theorem m13_11_9_12_0 : go 13 7 9 [11, 9, 12, 0] = true := by decide +kernel
theorem m13_11_9_12_1 : go 13 7 9 [11, 9, 12, 1] = true := by decide +kernel
theorem m13_11_9_12_2 : go 13 7 9 [11, 9, 12, 2] = true := by decide +kernel
theorem m13_11_9_12_3 : go 13 7 9 [11, 9, 12, 3] = true := by decide +kernel
theorem m13_11_9_12_4 : go 13 7 9 [11, 9, 12, 4] = true := by decide +kernel
theorem m13_11_9_12_5 : go 13 7 9 [11, 9, 12, 5] = true := by decide +kernel
theorem m13_11_9_12_6 : go 13 7 9 [11, 9, 12, 6] = true := by decide +kernel
theorem m13_11_9_12_10 : go 13 7 9 [11, 9, 12, 10] = true := by decide +kernel

theorem m13_11_9_12 : go 13 7 10 [11, 9, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_12_0
  · exact m13_11_9_12_1
  · exact m13_11_9_12_2
  · exact m13_11_9_12_3
  · exact m13_11_9_12_4
  · exact m13_11_9_12_5
  · exact m13_11_9_12_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_11_9 : go 13 7 11 [11, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_9_0
  · exact m13_11_9_1
  · exact m13_11_9_2
  · exact m13_11_9_3
  · exact m13_11_9_4
  · exact m13_11_9_5
  · exact m13_11_9_6
  · exact m13_11_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_9_12

end Misses
