import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 9]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_9_0_2 : go 13 7 9 [12, 9, 0, 2] = true := by decide +kernel
theorem m13_12_9_0_3 : go 13 7 9 [12, 9, 0, 3] = true := by decide +kernel
theorem m13_12_9_0_4 : go 13 7 9 [12, 9, 0, 4] = true := by decide +kernel
theorem m13_12_9_0_5 : go 13 7 9 [12, 9, 0, 5] = true := by decide +kernel
theorem m13_12_9_0_6 : go 13 7 9 [12, 9, 0, 6] = true := by decide +kernel
theorem m13_12_9_0_8 : go 13 7 9 [12, 9, 0, 8] = true := by decide +kernel
theorem m13_12_9_0_10 : go 13 7 9 [12, 9, 0, 10] = true := by decide +kernel

theorem m13_12_9_0 : go 13 7 10 [12, 9, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_0_2
  · exact m13_12_9_0_3
  · exact m13_12_9_0_4
  · exact m13_12_9_0_5
  · exact m13_12_9_0_6
  · exact absurd hs (by decide)
  · exact m13_12_9_0_8
  · exact absurd hs (by decide)
  · exact m13_12_9_0_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_1_3 : go 13 7 9 [12, 9, 1, 3] = true := by decide +kernel
theorem m13_12_9_1_4 : go 13 7 9 [12, 9, 1, 4] = true := by decide +kernel
theorem m13_12_9_1_5 : go 13 7 9 [12, 9, 1, 5] = true := by decide +kernel
theorem m13_12_9_1_6 : go 13 7 9 [12, 9, 1, 6] = true := by decide +kernel
theorem m13_12_9_1_8 : go 13 7 9 [12, 9, 1, 8] = true := by decide +kernel
theorem m13_12_9_1_10 : go 13 7 9 [12, 9, 1, 10] = true := by decide +kernel

theorem m13_12_9_1 : go 13 7 10 [12, 9, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_1_3
  · exact m13_12_9_1_4
  · exact m13_12_9_1_5
  · exact m13_12_9_1_6
  · exact absurd hs (by decide)
  · exact m13_12_9_1_8
  · exact absurd hs (by decide)
  · exact m13_12_9_1_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_2_0 : go 13 7 9 [12, 9, 2, 0] = true := by decide +kernel
theorem m13_12_9_2_4 : go 13 7 9 [12, 9, 2, 4] = true := by decide +kernel
theorem m13_12_9_2_5 : go 13 7 9 [12, 9, 2, 5] = true := by decide +kernel
theorem m13_12_9_2_6 : go 13 7 9 [12, 9, 2, 6] = true := by decide +kernel
theorem m13_12_9_2_8 : go 13 7 9 [12, 9, 2, 8] = true := by decide +kernel
theorem m13_12_9_2_10 : go 13 7 9 [12, 9, 2, 10] = true := by decide +kernel

theorem m13_12_9_2 : go 13 7 10 [12, 9, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_2_4
  · exact m13_12_9_2_5
  · exact m13_12_9_2_6
  · exact absurd hs (by decide)
  · exact m13_12_9_2_8
  · exact absurd hs (by decide)
  · exact m13_12_9_2_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_3_0 : go 13 7 9 [12, 9, 3, 0] = true := by decide +kernel
theorem m13_12_9_3_1 : go 13 7 9 [12, 9, 3, 1] = true := by decide +kernel
theorem m13_12_9_3_5 : go 13 7 9 [12, 9, 3, 5] = true := by decide +kernel
theorem m13_12_9_3_6 : go 13 7 9 [12, 9, 3, 6] = true := by decide +kernel
theorem m13_12_9_3_8 : go 13 7 9 [12, 9, 3, 8] = true := by decide +kernel
theorem m13_12_9_3_10 : go 13 7 9 [12, 9, 3, 10] = true := by decide +kernel

theorem m13_12_9_3 : go 13 7 10 [12, 9, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_3_0
  · exact m13_12_9_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_3_5
  · exact m13_12_9_3_6
  · exact absurd hs (by decide)
  · exact m13_12_9_3_8
  · exact absurd hs (by decide)
  · exact m13_12_9_3_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_4_0 : go 13 7 9 [12, 9, 4, 0] = true := by decide +kernel
theorem m13_12_9_4_1 : go 13 7 9 [12, 9, 4, 1] = true := by decide +kernel
theorem m13_12_9_4_2 : go 13 7 9 [12, 9, 4, 2] = true := by decide +kernel
theorem m13_12_9_4_6 : go 13 7 9 [12, 9, 4, 6] = true := by decide +kernel
theorem m13_12_9_4_8 : go 13 7 9 [12, 9, 4, 8] = true := by decide +kernel
theorem m13_12_9_4_10 : go 13 7 9 [12, 9, 4, 10] = true := by decide +kernel

theorem m13_12_9_4 : go 13 7 10 [12, 9, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_4_0
  · exact m13_12_9_4_1
  · exact m13_12_9_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_4_6
  · exact absurd hs (by decide)
  · exact m13_12_9_4_8
  · exact absurd hs (by decide)
  · exact m13_12_9_4_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_5_0 : go 13 7 9 [12, 9, 5, 0] = true := by decide +kernel
theorem m13_12_9_5_1 : go 13 7 9 [12, 9, 5, 1] = true := by decide +kernel
theorem m13_12_9_5_2 : go 13 7 9 [12, 9, 5, 2] = true := by decide +kernel
theorem m13_12_9_5_3 : go 13 7 9 [12, 9, 5, 3] = true := by decide +kernel
theorem m13_12_9_5_8 : go 13 7 9 [12, 9, 5, 8] = true := by decide +kernel
theorem m13_12_9_5_10 : go 13 7 9 [12, 9, 5, 10] = true := by decide +kernel

theorem m13_12_9_5 : go 13 7 10 [12, 9, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_5_0
  · exact m13_12_9_5_1
  · exact m13_12_9_5_2
  · exact m13_12_9_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_5_8
  · exact absurd hs (by decide)
  · exact m13_12_9_5_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_6_0 : go 13 7 9 [12, 9, 6, 0] = true := by decide +kernel
theorem m13_12_9_6_1 : go 13 7 9 [12, 9, 6, 1] = true := by decide +kernel
theorem m13_12_9_6_2 : go 13 7 9 [12, 9, 6, 2] = true := by decide +kernel
theorem m13_12_9_6_3 : go 13 7 9 [12, 9, 6, 3] = true := by decide +kernel
theorem m13_12_9_6_4 : go 13 7 9 [12, 9, 6, 4] = true := by decide +kernel
theorem m13_12_9_6_8 : go 13 7 9 [12, 9, 6, 8] = true := by decide +kernel
theorem m13_12_9_6_10 : go 13 7 9 [12, 9, 6, 10] = true := by decide +kernel

theorem m13_12_9_6 : go 13 7 10 [12, 9, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_6_0
  · exact m13_12_9_6_1
  · exact m13_12_9_6_2
  · exact m13_12_9_6_3
  · exact m13_12_9_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_6_8
  · exact absurd hs (by decide)
  · exact m13_12_9_6_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_7_0 : go 13 7 9 [12, 9, 7, 0] = true := by decide +kernel
theorem m13_12_9_7_1 : go 13 7 9 [12, 9, 7, 1] = true := by decide +kernel
theorem m13_12_9_7_2 : go 13 7 9 [12, 9, 7, 2] = true := by decide +kernel
theorem m13_12_9_7_3 : go 13 7 9 [12, 9, 7, 3] = true := by decide +kernel
theorem m13_12_9_7_4 : go 13 7 9 [12, 9, 7, 4] = true := by decide +kernel
theorem m13_12_9_7_5 : go 13 7 9 [12, 9, 7, 5] = true := by decide +kernel
theorem m13_12_9_7_10 : go 13 7 9 [12, 9, 7, 10] = true := by decide +kernel

theorem m13_12_9_7 : go 13 7 10 [12, 9, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_7_0
  · exact m13_12_9_7_1
  · exact m13_12_9_7_2
  · exact m13_12_9_7_3
  · exact m13_12_9_7_4
  · exact m13_12_9_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_7_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9_11_0 : go 13 7 9 [12, 9, 11, 0] = true := by decide +kernel
theorem m13_12_9_11_1 : go 13 7 9 [12, 9, 11, 1] = true := by decide +kernel
theorem m13_12_9_11_2 : go 13 7 9 [12, 9, 11, 2] = true := by decide +kernel
theorem m13_12_9_11_3 : go 13 7 9 [12, 9, 11, 3] = true := by decide +kernel
theorem m13_12_9_11_4 : go 13 7 9 [12, 9, 11, 4] = true := by decide +kernel
theorem m13_12_9_11_5 : go 13 7 9 [12, 9, 11, 5] = true := by decide +kernel
theorem m13_12_9_11_6 : go 13 7 9 [12, 9, 11, 6] = true := by decide +kernel
theorem m13_12_9_11_8 : go 13 7 9 [12, 9, 11, 8] = true := by decide +kernel

theorem m13_12_9_11 : go 13 7 10 [12, 9, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_11_0
  · exact m13_12_9_11_1
  · exact m13_12_9_11_2
  · exact m13_12_9_11_3
  · exact m13_12_9_11_4
  · exact m13_12_9_11_5
  · exact m13_12_9_11_6
  · exact absurd hs (by decide)
  · exact m13_12_9_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_9 : go 13 7 11 [12, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_9_0
  · exact m13_12_9_1
  · exact m13_12_9_2
  · exact m13_12_9_3
  · exact m13_12_9_4
  · exact m13_12_9_5
  · exact m13_12_9_6
  · exact m13_12_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_9_11
  · exact absurd hs (by decide)

end Misses
