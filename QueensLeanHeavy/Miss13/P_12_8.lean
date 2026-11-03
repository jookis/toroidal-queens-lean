import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 8]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_8_0_2 : go 13 7 9 [12, 8, 0, 2] = true := by decide +kernel
theorem m13_12_8_0_3 : go 13 7 9 [12, 8, 0, 3] = true := by decide +kernel
theorem m13_12_8_0_4 : go 13 7 9 [12, 8, 0, 4] = true := by decide +kernel
theorem m13_12_8_0_5 : go 13 7 9 [12, 8, 0, 5] = true := by decide +kernel
theorem m13_12_8_0_7 : go 13 7 9 [12, 8, 0, 7] = true := by decide +kernel
theorem m13_12_8_0_11 : go 13 7 9 [12, 8, 0, 11] = true := by decide +kernel

theorem m13_12_8_0 : go 13 7 10 [12, 8, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_0_2
  · exact m13_12_8_0_3
  · exact m13_12_8_0_4
  · exact m13_12_8_0_5
  · exact absurd hs (by decide)
  · exact m13_12_8_0_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_0_11
  · exact absurd hs (by decide)

theorem m13_12_8_1_3 : go 13 7 9 [12, 8, 1, 3] = true := by decide +kernel
theorem m13_12_8_1_4 : go 13 7 9 [12, 8, 1, 4] = true := by decide +kernel
theorem m13_12_8_1_5 : go 13 7 9 [12, 8, 1, 5] = true := by decide +kernel
theorem m13_12_8_1_7 : go 13 7 9 [12, 8, 1, 7] = true := by decide +kernel
theorem m13_12_8_1_11 : go 13 7 9 [12, 8, 1, 11] = true := by decide +kernel

theorem m13_12_8_1 : go 13 7 10 [12, 8, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_1_3
  · exact m13_12_8_1_4
  · exact m13_12_8_1_5
  · exact absurd hs (by decide)
  · exact m13_12_8_1_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_1_11
  · exact absurd hs (by decide)

theorem m13_12_8_2_0 : go 13 7 9 [12, 8, 2, 0] = true := by decide +kernel
theorem m13_12_8_2_4 : go 13 7 9 [12, 8, 2, 4] = true := by decide +kernel
theorem m13_12_8_2_5 : go 13 7 9 [12, 8, 2, 5] = true := by decide +kernel
theorem m13_12_8_2_7 : go 13 7 9 [12, 8, 2, 7] = true := by decide +kernel
theorem m13_12_8_2_11 : go 13 7 9 [12, 8, 2, 11] = true := by decide +kernel

theorem m13_12_8_2 : go 13 7 10 [12, 8, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_2_4
  · exact m13_12_8_2_5
  · exact absurd hs (by decide)
  · exact m13_12_8_2_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_2_11
  · exact absurd hs (by decide)

theorem m13_12_8_3_0 : go 13 7 9 [12, 8, 3, 0] = true := by decide +kernel
theorem m13_12_8_3_1 : go 13 7 9 [12, 8, 3, 1] = true := by decide +kernel
theorem m13_12_8_3_5 : go 13 7 9 [12, 8, 3, 5] = true := by decide +kernel
theorem m13_12_8_3_7 : go 13 7 9 [12, 8, 3, 7] = true := by decide +kernel
theorem m13_12_8_3_11 : go 13 7 9 [12, 8, 3, 11] = true := by decide +kernel

theorem m13_12_8_3 : go 13 7 10 [12, 8, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_3_0
  · exact m13_12_8_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_3_5
  · exact absurd hs (by decide)
  · exact m13_12_8_3_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_3_11
  · exact absurd hs (by decide)

theorem m13_12_8_4_0 : go 13 7 9 [12, 8, 4, 0] = true := by decide +kernel
theorem m13_12_8_4_1 : go 13 7 9 [12, 8, 4, 1] = true := by decide +kernel
theorem m13_12_8_4_2 : go 13 7 9 [12, 8, 4, 2] = true := by decide +kernel
theorem m13_12_8_4_7 : go 13 7 9 [12, 8, 4, 7] = true := by decide +kernel
theorem m13_12_8_4_11 : go 13 7 9 [12, 8, 4, 11] = true := by decide +kernel

theorem m13_12_8_4 : go 13 7 10 [12, 8, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_4_0
  · exact m13_12_8_4_1
  · exact m13_12_8_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_4_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_4_11
  · exact absurd hs (by decide)

theorem m13_12_8_5_0 : go 13 7 9 [12, 8, 5, 0] = true := by decide +kernel
theorem m13_12_8_5_1 : go 13 7 9 [12, 8, 5, 1] = true := by decide +kernel
theorem m13_12_8_5_2 : go 13 7 9 [12, 8, 5, 2] = true := by decide +kernel
theorem m13_12_8_5_3 : go 13 7 9 [12, 8, 5, 3] = true := by decide +kernel
theorem m13_12_8_5_7 : go 13 7 9 [12, 8, 5, 7] = true := by decide +kernel
theorem m13_12_8_5_11 : go 13 7 9 [12, 8, 5, 11] = true := by decide +kernel

theorem m13_12_8_5 : go 13 7 10 [12, 8, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_5_0
  · exact m13_12_8_5_1
  · exact m13_12_8_5_2
  · exact m13_12_8_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_5_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_5_11
  · exact absurd hs (by decide)

theorem m13_12_8_6_0 : go 13 7 9 [12, 8, 6, 0] = true := by decide +kernel
theorem m13_12_8_6_1 : go 13 7 9 [12, 8, 6, 1] = true := by decide +kernel
theorem m13_12_8_6_2 : go 13 7 9 [12, 8, 6, 2] = true := by decide +kernel
theorem m13_12_8_6_3 : go 13 7 9 [12, 8, 6, 3] = true := by decide +kernel
theorem m13_12_8_6_4 : go 13 7 9 [12, 8, 6, 4] = true := by decide +kernel
theorem m13_12_8_6_11 : go 13 7 9 [12, 8, 6, 11] = true := by decide +kernel

theorem m13_12_8_6 : go 13 7 10 [12, 8, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_6_0
  · exact m13_12_8_6_1
  · exact m13_12_8_6_2
  · exact m13_12_8_6_3
  · exact m13_12_8_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_6_11
  · exact absurd hs (by decide)

theorem m13_12_8_11_0 : go 13 7 9 [12, 8, 11, 0] = true := by decide +kernel
theorem m13_12_8_11_1 : go 13 7 9 [12, 8, 11, 1] = true := by decide +kernel
theorem m13_12_8_11_2 : go 13 7 9 [12, 8, 11, 2] = true := by decide +kernel
theorem m13_12_8_11_3 : go 13 7 9 [12, 8, 11, 3] = true := by decide +kernel
theorem m13_12_8_11_4 : go 13 7 9 [12, 8, 11, 4] = true := by decide +kernel
theorem m13_12_8_11_5 : go 13 7 9 [12, 8, 11, 5] = true := by decide +kernel
theorem m13_12_8_11_7 : go 13 7 9 [12, 8, 11, 7] = true := by decide +kernel

theorem m13_12_8_11 : go 13 7 10 [12, 8, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_11_0
  · exact m13_12_8_11_1
  · exact m13_12_8_11_2
  · exact m13_12_8_11_3
  · exact m13_12_8_11_4
  · exact m13_12_8_11_5
  · exact absurd hs (by decide)
  · exact m13_12_8_11_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_8 : go 13 7 11 [12, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_8_0
  · exact m13_12_8_1
  · exact m13_12_8_2
  · exact m13_12_8_3
  · exact m13_12_8_4
  · exact m13_12_8_5
  · exact m13_12_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_8_11
  · exact absurd hs (by decide)

end Misses
