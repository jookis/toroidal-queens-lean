import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [7, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_7_0_2_5 : go 13 7 9 [7, 0, 2, 5] = true := by decide +kernel
theorem m13_7_0_2_6 : go 13 7 9 [7, 0, 2, 6] = true := by decide +kernel
theorem m13_7_0_2_8 : go 13 7 9 [7, 0, 2, 8] = true := by decide +kernel
theorem m13_7_0_2_9 : go 13 7 9 [7, 0, 2, 9] = true := by decide +kernel
theorem m13_7_0_2_11 : go 13 7 9 [7, 0, 2, 11] = true := by decide +kernel
theorem m13_7_0_2_12 : go 13 7 9 [7, 0, 2, 12] = true := by decide +kernel

theorem m13_7_0_2 : go 13 7 10 [7, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_2_5
  · exact m13_7_0_2_6
  · exact absurd hs (by decide)
  · exact m13_7_0_2_8
  · exact m13_7_0_2_9
  · exact absurd hs (by decide)
  · exact m13_7_0_2_11
  · exact m13_7_0_2_12

theorem m13_7_0_3_1 : go 13 7 9 [7, 0, 3, 1] = true := by decide +kernel
theorem m13_7_0_3_5 : go 13 7 9 [7, 0, 3, 5] = true := by decide +kernel
theorem m13_7_0_3_6 : go 13 7 9 [7, 0, 3, 6] = true := by decide +kernel
theorem m13_7_0_3_8 : go 13 7 9 [7, 0, 3, 8] = true := by decide +kernel
theorem m13_7_0_3_9 : go 13 7 9 [7, 0, 3, 9] = true := by decide +kernel
theorem m13_7_0_3_11 : go 13 7 9 [7, 0, 3, 11] = true := by decide +kernel
theorem m13_7_0_3_12 : go 13 7 9 [7, 0, 3, 12] = true := by decide +kernel

theorem m13_7_0_3 : go 13 7 10 [7, 0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_3_5
  · exact m13_7_0_3_6
  · exact absurd hs (by decide)
  · exact m13_7_0_3_8
  · exact m13_7_0_3_9
  · exact absurd hs (by decide)
  · exact m13_7_0_3_11
  · exact m13_7_0_3_12

theorem m13_7_0_4_1 : go 13 7 9 [7, 0, 4, 1] = true := by decide +kernel
theorem m13_7_0_4_6 : go 13 7 9 [7, 0, 4, 6] = true := by decide +kernel
theorem m13_7_0_4_8 : go 13 7 9 [7, 0, 4, 8] = true := by decide +kernel
theorem m13_7_0_4_9 : go 13 7 9 [7, 0, 4, 9] = true := by decide +kernel
theorem m13_7_0_4_11 : go 13 7 9 [7, 0, 4, 11] = true := by decide +kernel
theorem m13_7_0_4_12 : go 13 7 9 [7, 0, 4, 12] = true := by decide +kernel

theorem m13_7_0_4 : go 13 7 10 [7, 0, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_4_6
  · exact absurd hs (by decide)
  · exact m13_7_0_4_8
  · exact m13_7_0_4_9
  · exact absurd hs (by decide)
  · exact m13_7_0_4_11
  · exact m13_7_0_4_12

theorem m13_7_0_6_1 : go 13 7 9 [7, 0, 6, 1] = true := by decide +kernel
theorem m13_7_0_6_3 : go 13 7 9 [7, 0, 6, 3] = true := by decide +kernel
theorem m13_7_0_6_8 : go 13 7 9 [7, 0, 6, 8] = true := by decide +kernel
theorem m13_7_0_6_9 : go 13 7 9 [7, 0, 6, 9] = true := by decide +kernel
theorem m13_7_0_6_11 : go 13 7 9 [7, 0, 6, 11] = true := by decide +kernel
theorem m13_7_0_6_12 : go 13 7 9 [7, 0, 6, 12] = true := by decide +kernel

theorem m13_7_0_6 : go 13 7 10 [7, 0, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_6_1
  · exact absurd hs (by decide)
  · exact m13_7_0_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_6_8
  · exact m13_7_0_6_9
  · exact absurd hs (by decide)
  · exact m13_7_0_6_11
  · exact m13_7_0_6_12

theorem m13_7_0_8_1 : go 13 7 9 [7, 0, 8, 1] = true := by decide +kernel
theorem m13_7_0_8_3 : go 13 7 9 [7, 0, 8, 3] = true := by decide +kernel
theorem m13_7_0_8_5 : go 13 7 9 [7, 0, 8, 5] = true := by decide +kernel
theorem m13_7_0_8_6 : go 13 7 9 [7, 0, 8, 6] = true := by decide +kernel
theorem m13_7_0_8_11 : go 13 7 9 [7, 0, 8, 11] = true := by decide +kernel
theorem m13_7_0_8_12 : go 13 7 9 [7, 0, 8, 12] = true := by decide +kernel

theorem m13_7_0_8 : go 13 7 10 [7, 0, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_8_1
  · exact absurd hs (by decide)
  · exact m13_7_0_8_3
  · exact absurd hs (by decide)
  · exact m13_7_0_8_5
  · exact m13_7_0_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_8_11
  · exact m13_7_0_8_12

theorem m13_7_0_10_1 : go 13 7 9 [7, 0, 10, 1] = true := by decide +kernel
theorem m13_7_0_10_3 : go 13 7 9 [7, 0, 10, 3] = true := by decide +kernel
theorem m13_7_0_10_5 : go 13 7 9 [7, 0, 10, 5] = true := by decide +kernel
theorem m13_7_0_10_6 : go 13 7 9 [7, 0, 10, 6] = true := by decide +kernel
theorem m13_7_0_10_8 : go 13 7 9 [7, 0, 10, 8] = true := by decide +kernel
theorem m13_7_0_10_12 : go 13 7 9 [7, 0, 10, 12] = true := by decide +kernel

theorem m13_7_0_10 : go 13 7 10 [7, 0, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_10_1
  · exact absurd hs (by decide)
  · exact m13_7_0_10_3
  · exact absurd hs (by decide)
  · exact m13_7_0_10_5
  · exact m13_7_0_10_6
  · exact absurd hs (by decide)
  · exact m13_7_0_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_10_12

theorem m13_7_0_11_1 : go 13 7 9 [7, 0, 11, 1] = true := by decide +kernel
theorem m13_7_0_11_3 : go 13 7 9 [7, 0, 11, 3] = true := by decide +kernel
theorem m13_7_0_11_5 : go 13 7 9 [7, 0, 11, 5] = true := by decide +kernel
theorem m13_7_0_11_6 : go 13 7 9 [7, 0, 11, 6] = true := by decide +kernel
theorem m13_7_0_11_8 : go 13 7 9 [7, 0, 11, 8] = true := by decide +kernel
theorem m13_7_0_11_9 : go 13 7 9 [7, 0, 11, 9] = true := by decide +kernel

theorem m13_7_0_11 : go 13 7 10 [7, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_11_1
  · exact absurd hs (by decide)
  · exact m13_7_0_11_3
  · exact absurd hs (by decide)
  · exact m13_7_0_11_5
  · exact m13_7_0_11_6
  · exact absurd hs (by decide)
  · exact m13_7_0_11_8
  · exact m13_7_0_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_7_0_12_1 : go 13 7 9 [7, 0, 12, 1] = true := by decide +kernel
theorem m13_7_0_12_3 : go 13 7 9 [7, 0, 12, 3] = true := by decide +kernel
theorem m13_7_0_12_5 : go 13 7 9 [7, 0, 12, 5] = true := by decide +kernel
theorem m13_7_0_12_6 : go 13 7 9 [7, 0, 12, 6] = true := by decide +kernel
theorem m13_7_0_12_8 : go 13 7 9 [7, 0, 12, 8] = true := by decide +kernel
theorem m13_7_0_12_9 : go 13 7 9 [7, 0, 12, 9] = true := by decide +kernel

theorem m13_7_0_12 : go 13 7 10 [7, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_7_0_12_1
  · exact absurd hs (by decide)
  · exact m13_7_0_12_3
  · exact absurd hs (by decide)
  · exact m13_7_0_12_5
  · exact m13_7_0_12_6
  · exact absurd hs (by decide)
  · exact m13_7_0_12_8
  · exact m13_7_0_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_7_0 : go 13 7 11 [7, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_0_2
  · exact m13_7_0_3
  · exact m13_7_0_4
  · exact absurd hs (by decide)
  · exact m13_7_0_6
  · exact absurd hs (by decide)
  · exact m13_7_0_8
  · exact absurd hs (by decide)
  · exact m13_7_0_10
  · exact m13_7_0_11
  · exact m13_7_0_12

end Misses
