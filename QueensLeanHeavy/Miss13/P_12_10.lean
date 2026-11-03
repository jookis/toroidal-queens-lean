import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_10_0_2 : go 13 7 9 [12, 10, 0, 2] = true := by decide +kernel
theorem m13_12_10_0_3 : go 13 7 9 [12, 10, 0, 3] = true := by decide +kernel
theorem m13_12_10_0_4 : go 13 7 9 [12, 10, 0, 4] = true := by decide +kernel
theorem m13_12_10_0_5 : go 13 7 9 [12, 10, 0, 5] = true := by decide +kernel
theorem m13_12_10_0_6 : go 13 7 9 [12, 10, 0, 6] = true := by decide +kernel
theorem m13_12_10_0_7 : go 13 7 9 [12, 10, 0, 7] = true := by decide +kernel
theorem m13_12_10_0_11 : go 13 7 9 [12, 10, 0, 11] = true := by decide +kernel

theorem m13_12_10_0 : go 13 7 10 [12, 10, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_0_2
  · exact m13_12_10_0_3
  · exact m13_12_10_0_4
  · exact m13_12_10_0_5
  · exact m13_12_10_0_6
  · exact m13_12_10_0_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_0_11
  · exact absurd hs (by decide)

theorem m13_12_10_1_3 : go 13 7 9 [12, 10, 1, 3] = true := by decide +kernel
theorem m13_12_10_1_4 : go 13 7 9 [12, 10, 1, 4] = true := by decide +kernel
theorem m13_12_10_1_5 : go 13 7 9 [12, 10, 1, 5] = true := by decide +kernel
theorem m13_12_10_1_6 : go 13 7 9 [12, 10, 1, 6] = true := by decide +kernel
theorem m13_12_10_1_7 : go 13 7 9 [12, 10, 1, 7] = true := by decide +kernel
theorem m13_12_10_1_11 : go 13 7 9 [12, 10, 1, 11] = true := by decide +kernel

theorem m13_12_10_1 : go 13 7 10 [12, 10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_1_3
  · exact m13_12_10_1_4
  · exact m13_12_10_1_5
  · exact m13_12_10_1_6
  · exact m13_12_10_1_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_1_11
  · exact absurd hs (by decide)

theorem m13_12_10_2_0 : go 13 7 9 [12, 10, 2, 0] = true := by decide +kernel
theorem m13_12_10_2_4 : go 13 7 9 [12, 10, 2, 4] = true := by decide +kernel
theorem m13_12_10_2_5 : go 13 7 9 [12, 10, 2, 5] = true := by decide +kernel
theorem m13_12_10_2_6 : go 13 7 9 [12, 10, 2, 6] = true := by decide +kernel
theorem m13_12_10_2_7 : go 13 7 9 [12, 10, 2, 7] = true := by decide +kernel
theorem m13_12_10_2_11 : go 13 7 9 [12, 10, 2, 11] = true := by decide +kernel

theorem m13_12_10_2 : go 13 7 10 [12, 10, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_2_4
  · exact m13_12_10_2_5
  · exact m13_12_10_2_6
  · exact m13_12_10_2_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_2_11
  · exact absurd hs (by decide)

theorem m13_12_10_3_0 : go 13 7 9 [12, 10, 3, 0] = true := by decide +kernel
theorem m13_12_10_3_1 : go 13 7 9 [12, 10, 3, 1] = true := by decide +kernel
theorem m13_12_10_3_5 : go 13 7 9 [12, 10, 3, 5] = true := by decide +kernel
theorem m13_12_10_3_6 : go 13 7 9 [12, 10, 3, 6] = true := by decide +kernel
theorem m13_12_10_3_7 : go 13 7 9 [12, 10, 3, 7] = true := by decide +kernel
theorem m13_12_10_3_11 : go 13 7 9 [12, 10, 3, 11] = true := by decide +kernel

theorem m13_12_10_3 : go 13 7 10 [12, 10, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_3_0
  · exact m13_12_10_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_3_5
  · exact m13_12_10_3_6
  · exact m13_12_10_3_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_3_11
  · exact absurd hs (by decide)

theorem m13_12_10_4_0 : go 13 7 9 [12, 10, 4, 0] = true := by decide +kernel
theorem m13_12_10_4_1 : go 13 7 9 [12, 10, 4, 1] = true := by decide +kernel
theorem m13_12_10_4_2 : go 13 7 9 [12, 10, 4, 2] = true := by decide +kernel
theorem m13_12_10_4_6 : go 13 7 9 [12, 10, 4, 6] = true := by decide +kernel
theorem m13_12_10_4_7 : go 13 7 9 [12, 10, 4, 7] = true := by decide +kernel
theorem m13_12_10_4_11 : go 13 7 9 [12, 10, 4, 11] = true := by decide +kernel

theorem m13_12_10_4 : go 13 7 10 [12, 10, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_4_0
  · exact m13_12_10_4_1
  · exact m13_12_10_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_4_6
  · exact m13_12_10_4_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_4_11
  · exact absurd hs (by decide)

theorem m13_12_10_5_0 : go 13 7 9 [12, 10, 5, 0] = true := by decide +kernel
theorem m13_12_10_5_1 : go 13 7 9 [12, 10, 5, 1] = true := by decide +kernel
theorem m13_12_10_5_2 : go 13 7 9 [12, 10, 5, 2] = true := by decide +kernel
theorem m13_12_10_5_3 : go 13 7 9 [12, 10, 5, 3] = true := by decide +kernel
theorem m13_12_10_5_7 : go 13 7 9 [12, 10, 5, 7] = true := by decide +kernel
theorem m13_12_10_5_11 : go 13 7 9 [12, 10, 5, 11] = true := by decide +kernel

theorem m13_12_10_5 : go 13 7 10 [12, 10, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_5_0
  · exact m13_12_10_5_1
  · exact m13_12_10_5_2
  · exact m13_12_10_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_5_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_5_11
  · exact absurd hs (by decide)

theorem m13_12_10_6_0 : go 13 7 9 [12, 10, 6, 0] = true := by decide +kernel
theorem m13_12_10_6_1 : go 13 7 9 [12, 10, 6, 1] = true := by decide +kernel
theorem m13_12_10_6_2 : go 13 7 9 [12, 10, 6, 2] = true := by decide +kernel
theorem m13_12_10_6_3 : go 13 7 9 [12, 10, 6, 3] = true := by decide +kernel
theorem m13_12_10_6_4 : go 13 7 9 [12, 10, 6, 4] = true := by decide +kernel
theorem m13_12_10_6_11 : go 13 7 9 [12, 10, 6, 11] = true := by decide +kernel

theorem m13_12_10_6 : go 13 7 10 [12, 10, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_6_0
  · exact m13_12_10_6_1
  · exact m13_12_10_6_2
  · exact m13_12_10_6_3
  · exact m13_12_10_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_6_11
  · exact absurd hs (by decide)

theorem m13_12_10_7_0 : go 13 7 9 [12, 10, 7, 0] = true := by decide +kernel
theorem m13_12_10_7_1 : go 13 7 9 [12, 10, 7, 1] = true := by decide +kernel
theorem m13_12_10_7_2 : go 13 7 9 [12, 10, 7, 2] = true := by decide +kernel
theorem m13_12_10_7_3 : go 13 7 9 [12, 10, 7, 3] = true := by decide +kernel
theorem m13_12_10_7_4 : go 13 7 9 [12, 10, 7, 4] = true := by decide +kernel
theorem m13_12_10_7_5 : go 13 7 9 [12, 10, 7, 5] = true := by decide +kernel
theorem m13_12_10_7_11 : go 13 7 9 [12, 10, 7, 11] = true := by decide +kernel

theorem m13_12_10_7 : go 13 7 10 [12, 10, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_7_0
  · exact m13_12_10_7_1
  · exact m13_12_10_7_2
  · exact m13_12_10_7_3
  · exact m13_12_10_7_4
  · exact m13_12_10_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_7_11
  · exact absurd hs (by decide)

theorem m13_12_10_8_0 : go 13 7 9 [12, 10, 8, 0] = true := by decide +kernel
theorem m13_12_10_8_1 : go 13 7 9 [12, 10, 8, 1] = true := by decide +kernel
theorem m13_12_10_8_2 : go 13 7 9 [12, 10, 8, 2] = true := by decide +kernel
theorem m13_12_10_8_3 : go 13 7 9 [12, 10, 8, 3] = true := by decide +kernel
theorem m13_12_10_8_4 : go 13 7 9 [12, 10, 8, 4] = true := by decide +kernel
theorem m13_12_10_8_5 : go 13 7 9 [12, 10, 8, 5] = true := by decide +kernel
theorem m13_12_10_8_6 : go 13 7 9 [12, 10, 8, 6] = true := by decide +kernel
theorem m13_12_10_8_11 : go 13 7 9 [12, 10, 8, 11] = true := by decide +kernel

theorem m13_12_10_8 : go 13 7 10 [12, 10, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_8_0
  · exact m13_12_10_8_1
  · exact m13_12_10_8_2
  · exact m13_12_10_8_3
  · exact m13_12_10_8_4
  · exact m13_12_10_8_5
  · exact m13_12_10_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_10_8_11
  · exact absurd hs (by decide)

theorem m13_12_10 : go 13 7 11 [12, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_10_0
  · exact m13_12_10_1
  · exact m13_12_10_2
  · exact m13_12_10_3
  · exact m13_12_10_4
  · exact m13_12_10_5
  · exact m13_12_10_6
  · exact m13_12_10_7
  · exact m13_12_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
