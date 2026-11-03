import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [6, 8]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_6_8_0_2 : go 13 7 9 [6, 8, 0, 2] = true := by decide +kernel
theorem m13_6_8_0_4 : go 13 7 9 [6, 8, 0, 4] = true := by decide +kernel
theorem m13_6_8_0_5 : go 13 7 9 [6, 8, 0, 5] = true := by decide +kernel
theorem m13_6_8_0_7 : go 13 7 9 [6, 8, 0, 7] = true := by decide +kernel
theorem m13_6_8_0_11 : go 13 7 9 [6, 8, 0, 11] = true := by decide +kernel
theorem m13_6_8_0_12 : go 13 7 9 [6, 8, 0, 12] = true := by decide +kernel

theorem m13_6_8_0 : go 13 7 10 [6, 8, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_0_2
  · exact absurd hs (by decide)
  · exact m13_6_8_0_4
  · exact m13_6_8_0_5
  · exact absurd hs (by decide)
  · exact m13_6_8_0_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_0_11
  · exact m13_6_8_0_12

theorem m13_6_8_1_4 : go 13 7 9 [6, 8, 1, 4] = true := by decide +kernel
theorem m13_6_8_1_5 : go 13 7 9 [6, 8, 1, 5] = true := by decide +kernel
theorem m13_6_8_1_7 : go 13 7 9 [6, 8, 1, 7] = true := by decide +kernel
theorem m13_6_8_1_11 : go 13 7 9 [6, 8, 1, 11] = true := by decide +kernel
theorem m13_6_8_1_12 : go 13 7 9 [6, 8, 1, 12] = true := by decide +kernel

theorem m13_6_8_1 : go 13 7 10 [6, 8, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_1_4
  · exact m13_6_8_1_5
  · exact absurd hs (by decide)
  · exact m13_6_8_1_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_1_11
  · exact m13_6_8_1_12

theorem m13_6_8_2_0 : go 13 7 9 [6, 8, 2, 0] = true := by decide +kernel
theorem m13_6_8_2_4 : go 13 7 9 [6, 8, 2, 4] = true := by decide +kernel
theorem m13_6_8_2_5 : go 13 7 9 [6, 8, 2, 5] = true := by decide +kernel
theorem m13_6_8_2_7 : go 13 7 9 [6, 8, 2, 7] = true := by decide +kernel
theorem m13_6_8_2_11 : go 13 7 9 [6, 8, 2, 11] = true := by decide +kernel
theorem m13_6_8_2_12 : go 13 7 9 [6, 8, 2, 12] = true := by decide +kernel

theorem m13_6_8_2 : go 13 7 10 [6, 8, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_2_4
  · exact m13_6_8_2_5
  · exact absurd hs (by decide)
  · exact m13_6_8_2_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_2_11
  · exact m13_6_8_2_12

theorem m13_6_8_3_0 : go 13 7 9 [6, 8, 3, 0] = true := by decide +kernel
theorem m13_6_8_3_1 : go 13 7 9 [6, 8, 3, 1] = true := by decide +kernel
theorem m13_6_8_3_5 : go 13 7 9 [6, 8, 3, 5] = true := by decide +kernel
theorem m13_6_8_3_7 : go 13 7 9 [6, 8, 3, 7] = true := by decide +kernel
theorem m13_6_8_3_11 : go 13 7 9 [6, 8, 3, 11] = true := by decide +kernel
theorem m13_6_8_3_12 : go 13 7 9 [6, 8, 3, 12] = true := by decide +kernel

theorem m13_6_8_3 : go 13 7 10 [6, 8, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_3_0
  · exact m13_6_8_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_3_5
  · exact absurd hs (by decide)
  · exact m13_6_8_3_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_3_11
  · exact m13_6_8_3_12

theorem m13_6_8_5_0 : go 13 7 9 [6, 8, 5, 0] = true := by decide +kernel
theorem m13_6_8_5_1 : go 13 7 9 [6, 8, 5, 1] = true := by decide +kernel
theorem m13_6_8_5_2 : go 13 7 9 [6, 8, 5, 2] = true := by decide +kernel
theorem m13_6_8_5_7 : go 13 7 9 [6, 8, 5, 7] = true := by decide +kernel
theorem m13_6_8_5_11 : go 13 7 9 [6, 8, 5, 11] = true := by decide +kernel
theorem m13_6_8_5_12 : go 13 7 9 [6, 8, 5, 12] = true := by decide +kernel

theorem m13_6_8_5 : go 13 7 10 [6, 8, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_5_0
  · exact m13_6_8_5_1
  · exact m13_6_8_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_5_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_5_11
  · exact m13_6_8_5_12

theorem m13_6_8_10_0 : go 13 7 9 [6, 8, 10, 0] = true := by decide +kernel
theorem m13_6_8_10_1 : go 13 7 9 [6, 8, 10, 1] = true := by decide +kernel
theorem m13_6_8_10_2 : go 13 7 9 [6, 8, 10, 2] = true := by decide +kernel
theorem m13_6_8_10_4 : go 13 7 9 [6, 8, 10, 4] = true := by decide +kernel
theorem m13_6_8_10_5 : go 13 7 9 [6, 8, 10, 5] = true := by decide +kernel
theorem m13_6_8_10_7 : go 13 7 9 [6, 8, 10, 7] = true := by decide +kernel
theorem m13_6_8_10_12 : go 13 7 9 [6, 8, 10, 12] = true := by decide +kernel

theorem m13_6_8_10 : go 13 7 10 [6, 8, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_10_0
  · exact m13_6_8_10_1
  · exact m13_6_8_10_2
  · exact absurd hs (by decide)
  · exact m13_6_8_10_4
  · exact m13_6_8_10_5
  · exact absurd hs (by decide)
  · exact m13_6_8_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_10_12

theorem m13_6_8_11_0 : go 13 7 9 [6, 8, 11, 0] = true := by decide +kernel
theorem m13_6_8_11_1 : go 13 7 9 [6, 8, 11, 1] = true := by decide +kernel
theorem m13_6_8_11_2 : go 13 7 9 [6, 8, 11, 2] = true := by decide +kernel
theorem m13_6_8_11_4 : go 13 7 9 [6, 8, 11, 4] = true := by decide +kernel
theorem m13_6_8_11_5 : go 13 7 9 [6, 8, 11, 5] = true := by decide +kernel
theorem m13_6_8_11_7 : go 13 7 9 [6, 8, 11, 7] = true := by decide +kernel

theorem m13_6_8_11 : go 13 7 10 [6, 8, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_11_0
  · exact m13_6_8_11_1
  · exact m13_6_8_11_2
  · exact absurd hs (by decide)
  · exact m13_6_8_11_4
  · exact m13_6_8_11_5
  · exact absurd hs (by decide)
  · exact m13_6_8_11_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_8_12_0 : go 13 7 9 [6, 8, 12, 0] = true := by decide +kernel
theorem m13_6_8_12_1 : go 13 7 9 [6, 8, 12, 1] = true := by decide +kernel
theorem m13_6_8_12_2 : go 13 7 9 [6, 8, 12, 2] = true := by decide +kernel
theorem m13_6_8_12_4 : go 13 7 9 [6, 8, 12, 4] = true := by decide +kernel
theorem m13_6_8_12_5 : go 13 7 9 [6, 8, 12, 5] = true := by decide +kernel
theorem m13_6_8_12_7 : go 13 7 9 [6, 8, 12, 7] = true := by decide +kernel

theorem m13_6_8_12 : go 13 7 10 [6, 8, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_12_0
  · exact m13_6_8_12_1
  · exact m13_6_8_12_2
  · exact absurd hs (by decide)
  · exact m13_6_8_12_4
  · exact m13_6_8_12_5
  · exact absurd hs (by decide)
  · exact m13_6_8_12_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_8 : go 13 7 11 [6, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_8_0
  · exact m13_6_8_1
  · exact m13_6_8_2
  · exact m13_6_8_3
  · exact absurd hs (by decide)
  · exact m13_6_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_8_10
  · exact m13_6_8_11
  · exact m13_6_8_12

end Misses
