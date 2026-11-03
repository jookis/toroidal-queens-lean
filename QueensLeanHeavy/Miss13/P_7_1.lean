import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [7, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_7_1_3_0 : go 13 7 9 [7, 1, 3, 0] = true := by decide +kernel
theorem m13_7_1_3_5 : go 13 7 9 [7, 1, 3, 5] = true := by decide +kernel
theorem m13_7_1_3_6 : go 13 7 9 [7, 1, 3, 6] = true := by decide +kernel
theorem m13_7_1_3_8 : go 13 7 9 [7, 1, 3, 8] = true := by decide +kernel
theorem m13_7_1_3_9 : go 13 7 9 [7, 1, 3, 9] = true := by decide +kernel
theorem m13_7_1_3_11 : go 13 7 9 [7, 1, 3, 11] = true := by decide +kernel
theorem m13_7_1_3_12 : go 13 7 9 [7, 1, 3, 12] = true := by decide +kernel

theorem m13_7_1_3 : go 13 7 10 [7, 1, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_3_5
  · exact m13_7_1_3_6
  · exact absurd hs (by decide)
  · exact m13_7_1_3_8
  · exact m13_7_1_3_9
  · exact absurd hs (by decide)
  · exact m13_7_1_3_11
  · exact m13_7_1_3_12

theorem m13_7_1_4_0 : go 13 7 9 [7, 1, 4, 0] = true := by decide +kernel
theorem m13_7_1_4_2 : go 13 7 9 [7, 1, 4, 2] = true := by decide +kernel
theorem m13_7_1_4_6 : go 13 7 9 [7, 1, 4, 6] = true := by decide +kernel
theorem m13_7_1_4_8 : go 13 7 9 [7, 1, 4, 8] = true := by decide +kernel
theorem m13_7_1_4_9 : go 13 7 9 [7, 1, 4, 9] = true := by decide +kernel
theorem m13_7_1_4_11 : go 13 7 9 [7, 1, 4, 11] = true := by decide +kernel
theorem m13_7_1_4_12 : go 13 7 9 [7, 1, 4, 12] = true := by decide +kernel

theorem m13_7_1_4 : go 13 7 10 [7, 1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_4_0
  · exact absurd hs (by decide)
  · exact m13_7_1_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_4_6
  · exact absurd hs (by decide)
  · exact m13_7_1_4_8
  · exact m13_7_1_4_9
  · exact absurd hs (by decide)
  · exact m13_7_1_4_11
  · exact m13_7_1_4_12

theorem m13_7_1_6_0 : go 13 7 9 [7, 1, 6, 0] = true := by decide +kernel
theorem m13_7_1_6_2 : go 13 7 9 [7, 1, 6, 2] = true := by decide +kernel
theorem m13_7_1_6_8 : go 13 7 9 [7, 1, 6, 8] = true := by decide +kernel
theorem m13_7_1_6_9 : go 13 7 9 [7, 1, 6, 9] = true := by decide +kernel
theorem m13_7_1_6_11 : go 13 7 9 [7, 1, 6, 11] = true := by decide +kernel
theorem m13_7_1_6_12 : go 13 7 9 [7, 1, 6, 12] = true := by decide +kernel

theorem m13_7_1_6 : go 13 7 10 [7, 1, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_6_0
  · exact absurd hs (by decide)
  · exact m13_7_1_6_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_6_8
  · exact m13_7_1_6_9
  · exact absurd hs (by decide)
  · exact m13_7_1_6_11
  · exact m13_7_1_6_12

theorem m13_7_1_8_0 : go 13 7 9 [7, 1, 8, 0] = true := by decide +kernel
theorem m13_7_1_8_2 : go 13 7 9 [7, 1, 8, 2] = true := by decide +kernel
theorem m13_7_1_8_5 : go 13 7 9 [7, 1, 8, 5] = true := by decide +kernel
theorem m13_7_1_8_6 : go 13 7 9 [7, 1, 8, 6] = true := by decide +kernel
theorem m13_7_1_8_11 : go 13 7 9 [7, 1, 8, 11] = true := by decide +kernel
theorem m13_7_1_8_12 : go 13 7 9 [7, 1, 8, 12] = true := by decide +kernel

theorem m13_7_1_8 : go 13 7 10 [7, 1, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_8_0
  · exact absurd hs (by decide)
  · exact m13_7_1_8_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_8_5
  · exact m13_7_1_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_8_11
  · exact m13_7_1_8_12

theorem m13_7_1_10_0 : go 13 7 9 [7, 1, 10, 0] = true := by decide +kernel
theorem m13_7_1_10_2 : go 13 7 9 [7, 1, 10, 2] = true := by decide +kernel
theorem m13_7_1_10_5 : go 13 7 9 [7, 1, 10, 5] = true := by decide +kernel
theorem m13_7_1_10_6 : go 13 7 9 [7, 1, 10, 6] = true := by decide +kernel
theorem m13_7_1_10_8 : go 13 7 9 [7, 1, 10, 8] = true := by decide +kernel
theorem m13_7_1_10_12 : go 13 7 9 [7, 1, 10, 12] = true := by decide +kernel

theorem m13_7_1_10 : go 13 7 10 [7, 1, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_10_0
  · exact absurd hs (by decide)
  · exact m13_7_1_10_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_10_5
  · exact m13_7_1_10_6
  · exact absurd hs (by decide)
  · exact m13_7_1_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_10_12

theorem m13_7_1_11_0 : go 13 7 9 [7, 1, 11, 0] = true := by decide +kernel
theorem m13_7_1_11_2 : go 13 7 9 [7, 1, 11, 2] = true := by decide +kernel
theorem m13_7_1_11_5 : go 13 7 9 [7, 1, 11, 5] = true := by decide +kernel
theorem m13_7_1_11_6 : go 13 7 9 [7, 1, 11, 6] = true := by decide +kernel
theorem m13_7_1_11_8 : go 13 7 9 [7, 1, 11, 8] = true := by decide +kernel
theorem m13_7_1_11_9 : go 13 7 9 [7, 1, 11, 9] = true := by decide +kernel

theorem m13_7_1_11 : go 13 7 10 [7, 1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_11_0
  · exact absurd hs (by decide)
  · exact m13_7_1_11_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_11_5
  · exact m13_7_1_11_6
  · exact absurd hs (by decide)
  · exact m13_7_1_11_8
  · exact m13_7_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_7_1_12_0 : go 13 7 9 [7, 1, 12, 0] = true := by decide +kernel
theorem m13_7_1_12_2 : go 13 7 9 [7, 1, 12, 2] = true := by decide +kernel
theorem m13_7_1_12_5 : go 13 7 9 [7, 1, 12, 5] = true := by decide +kernel
theorem m13_7_1_12_6 : go 13 7 9 [7, 1, 12, 6] = true := by decide +kernel
theorem m13_7_1_12_8 : go 13 7 9 [7, 1, 12, 8] = true := by decide +kernel
theorem m13_7_1_12_9 : go 13 7 9 [7, 1, 12, 9] = true := by decide +kernel

theorem m13_7_1_12 : go 13 7 10 [7, 1, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_7_1_12_0
  · exact absurd hs (by decide)
  · exact m13_7_1_12_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_12_5
  · exact m13_7_1_12_6
  · exact absurd hs (by decide)
  · exact m13_7_1_12_8
  · exact m13_7_1_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_7_1 : go 13 7 11 [7, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_7_1_3
  · exact m13_7_1_4
  · exact absurd hs (by decide)
  · exact m13_7_1_6
  · exact absurd hs (by decide)
  · exact m13_7_1_8
  · exact absurd hs (by decide)
  · exact m13_7_1_10
  · exact m13_7_1_11
  · exact m13_7_1_12

end Misses
