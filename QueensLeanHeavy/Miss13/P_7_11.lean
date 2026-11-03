import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [7, 11]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_7_11_0_2 : go 13 7 9 [7, 11, 0, 2] = true := by decide +kernel
theorem m13_7_11_0_3 : go 13 7 9 [7, 11, 0, 3] = true := by decide +kernel
theorem m13_7_11_0_5 : go 13 7 9 [7, 11, 0, 5] = true := by decide +kernel
theorem m13_7_11_0_6 : go 13 7 9 [7, 11, 0, 6] = true := by decide +kernel
theorem m13_7_11_0_8 : go 13 7 9 [7, 11, 0, 8] = true := by decide +kernel
theorem m13_7_11_0_12 : go 13 7 9 [7, 11, 0, 12] = true := by decide +kernel

theorem m13_7_11_0 : go 13 7 10 [7, 11, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_0_2
  · exact m13_7_11_0_3
  · exact absurd hs (by decide)
  · exact m13_7_11_0_5
  · exact m13_7_11_0_6
  · exact absurd hs (by decide)
  · exact m13_7_11_0_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_0_12

theorem m13_7_11_1_3 : go 13 7 9 [7, 11, 1, 3] = true := by decide +kernel
theorem m13_7_11_1_5 : go 13 7 9 [7, 11, 1, 5] = true := by decide +kernel
theorem m13_7_11_1_6 : go 13 7 9 [7, 11, 1, 6] = true := by decide +kernel
theorem m13_7_11_1_8 : go 13 7 9 [7, 11, 1, 8] = true := by decide +kernel
theorem m13_7_11_1_12 : go 13 7 9 [7, 11, 1, 12] = true := by decide +kernel

theorem m13_7_11_1 : go 13 7 10 [7, 11, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_1_3
  · exact absurd hs (by decide)
  · exact m13_7_11_1_5
  · exact m13_7_11_1_6
  · exact absurd hs (by decide)
  · exact m13_7_11_1_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_1_12

theorem m13_7_11_2_0 : go 13 7 9 [7, 11, 2, 0] = true := by decide +kernel
theorem m13_7_11_2_5 : go 13 7 9 [7, 11, 2, 5] = true := by decide +kernel
theorem m13_7_11_2_6 : go 13 7 9 [7, 11, 2, 6] = true := by decide +kernel
theorem m13_7_11_2_8 : go 13 7 9 [7, 11, 2, 8] = true := by decide +kernel
theorem m13_7_11_2_12 : go 13 7 9 [7, 11, 2, 12] = true := by decide +kernel

theorem m13_7_11_2 : go 13 7 10 [7, 11, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_11_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_2_5
  · exact m13_7_11_2_6
  · exact absurd hs (by decide)
  · exact m13_7_11_2_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_2_12

theorem m13_7_11_3_0 : go 13 7 9 [7, 11, 3, 0] = true := by decide +kernel
theorem m13_7_11_3_1 : go 13 7 9 [7, 11, 3, 1] = true := by decide +kernel
theorem m13_7_11_3_5 : go 13 7 9 [7, 11, 3, 5] = true := by decide +kernel
theorem m13_7_11_3_6 : go 13 7 9 [7, 11, 3, 6] = true := by decide +kernel
theorem m13_7_11_3_8 : go 13 7 9 [7, 11, 3, 8] = true := by decide +kernel
theorem m13_7_11_3_12 : go 13 7 9 [7, 11, 3, 12] = true := by decide +kernel

theorem m13_7_11_3 : go 13 7 10 [7, 11, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_11_3_0
  · exact m13_7_11_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_3_5
  · exact m13_7_11_3_6
  · exact absurd hs (by decide)
  · exact m13_7_11_3_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_3_12

theorem m13_7_11_4_0 : go 13 7 9 [7, 11, 4, 0] = true := by decide +kernel
theorem m13_7_11_4_1 : go 13 7 9 [7, 11, 4, 1] = true := by decide +kernel
theorem m13_7_11_4_2 : go 13 7 9 [7, 11, 4, 2] = true := by decide +kernel
theorem m13_7_11_4_6 : go 13 7 9 [7, 11, 4, 6] = true := by decide +kernel
theorem m13_7_11_4_8 : go 13 7 9 [7, 11, 4, 8] = true := by decide +kernel
theorem m13_7_11_4_12 : go 13 7 9 [7, 11, 4, 12] = true := by decide +kernel

theorem m13_7_11_4 : go 13 7 10 [7, 11, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_11_4_0
  · exact m13_7_11_4_1
  · exact m13_7_11_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_4_6
  · exact absurd hs (by decide)
  · exact m13_7_11_4_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_4_12

theorem m13_7_11_6_0 : go 13 7 9 [7, 11, 6, 0] = true := by decide +kernel
theorem m13_7_11_6_1 : go 13 7 9 [7, 11, 6, 1] = true := by decide +kernel
theorem m13_7_11_6_2 : go 13 7 9 [7, 11, 6, 2] = true := by decide +kernel
theorem m13_7_11_6_3 : go 13 7 9 [7, 11, 6, 3] = true := by decide +kernel
theorem m13_7_11_6_8 : go 13 7 9 [7, 11, 6, 8] = true := by decide +kernel
theorem m13_7_11_6_12 : go 13 7 9 [7, 11, 6, 12] = true := by decide +kernel

theorem m13_7_11_6 : go 13 7 10 [7, 11, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_11_6_0
  · exact m13_7_11_6_1
  · exact m13_7_11_6_2
  · exact m13_7_11_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_6_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_6_12

theorem m13_7_11_8_0 : go 13 7 9 [7, 11, 8, 0] = true := by decide +kernel
theorem m13_7_11_8_1 : go 13 7 9 [7, 11, 8, 1] = true := by decide +kernel
theorem m13_7_11_8_2 : go 13 7 9 [7, 11, 8, 2] = true := by decide +kernel
theorem m13_7_11_8_3 : go 13 7 9 [7, 11, 8, 3] = true := by decide +kernel
theorem m13_7_11_8_5 : go 13 7 9 [7, 11, 8, 5] = true := by decide +kernel
theorem m13_7_11_8_6 : go 13 7 9 [7, 11, 8, 6] = true := by decide +kernel
theorem m13_7_11_8_12 : go 13 7 9 [7, 11, 8, 12] = true := by decide +kernel

theorem m13_7_11_8 : go 13 7 10 [7, 11, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_11_8_0
  · exact m13_7_11_8_1
  · exact m13_7_11_8_2
  · exact m13_7_11_8_3
  · exact absurd hs (by decide)
  · exact m13_7_11_8_5
  · exact m13_7_11_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_11_8_12

theorem m13_7_11 : go 13 7 11 [7, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_11_0
  · exact m13_7_11_1
  · exact m13_7_11_2
  · exact m13_7_11_3
  · exact m13_7_11_4
  · exact absurd hs (by decide)
  · exact m13_7_11_6
  · exact absurd hs (by decide)
  · exact m13_7_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
