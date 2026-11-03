import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [11, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_11_1_3_0 : go 13 7 9 [11, 1, 3, 0] = true := by decide +kernel
theorem m13_11_1_3_5 : go 13 7 9 [11, 1, 3, 5] = true := by decide +kernel
theorem m13_11_1_3_6 : go 13 7 9 [11, 1, 3, 6] = true := by decide +kernel
theorem m13_11_1_3_7 : go 13 7 9 [11, 1, 3, 7] = true := by decide +kernel
theorem m13_11_1_3_9 : go 13 7 9 [11, 1, 3, 9] = true := by decide +kernel
theorem m13_11_1_3_10 : go 13 7 9 [11, 1, 3, 10] = true := by decide +kernel
theorem m13_11_1_3_12 : go 13 7 9 [11, 1, 3, 12] = true := by decide +kernel

theorem m13_11_1_3 : go 13 7 10 [11, 1, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_3_5
  · exact m13_11_1_3_6
  · exact m13_11_1_3_7
  · exact absurd hs (by decide)
  · exact m13_11_1_3_9
  · exact m13_11_1_3_10
  · exact absurd hs (by decide)
  · exact m13_11_1_3_12

theorem m13_11_1_4_0 : go 13 7 9 [11, 1, 4, 0] = true := by decide +kernel
theorem m13_11_1_4_2 : go 13 7 9 [11, 1, 4, 2] = true := by decide +kernel
theorem m13_11_1_4_6 : go 13 7 9 [11, 1, 4, 6] = true := by decide +kernel
theorem m13_11_1_4_7 : go 13 7 9 [11, 1, 4, 7] = true := by decide +kernel
theorem m13_11_1_4_9 : go 13 7 9 [11, 1, 4, 9] = true := by decide +kernel
theorem m13_11_1_4_10 : go 13 7 9 [11, 1, 4, 10] = true := by decide +kernel
theorem m13_11_1_4_12 : go 13 7 9 [11, 1, 4, 12] = true := by decide +kernel

theorem m13_11_1_4 : go 13 7 10 [11, 1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_4_0
  · exact absurd hs (by decide)
  · exact m13_11_1_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_4_6
  · exact m13_11_1_4_7
  · exact absurd hs (by decide)
  · exact m13_11_1_4_9
  · exact m13_11_1_4_10
  · exact absurd hs (by decide)
  · exact m13_11_1_4_12

theorem m13_11_1_5_0 : go 13 7 9 [11, 1, 5, 0] = true := by decide +kernel
theorem m13_11_1_5_2 : go 13 7 9 [11, 1, 5, 2] = true := by decide +kernel
theorem m13_11_1_5_7 : go 13 7 9 [11, 1, 5, 7] = true := by decide +kernel
theorem m13_11_1_5_9 : go 13 7 9 [11, 1, 5, 9] = true := by decide +kernel
theorem m13_11_1_5_10 : go 13 7 9 [11, 1, 5, 10] = true := by decide +kernel
theorem m13_11_1_5_12 : go 13 7 9 [11, 1, 5, 12] = true := by decide +kernel

theorem m13_11_1_5 : go 13 7 10 [11, 1, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_5_0
  · exact absurd hs (by decide)
  · exact m13_11_1_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_5_7
  · exact absurd hs (by decide)
  · exact m13_11_1_5_9
  · exact m13_11_1_5_10
  · exact absurd hs (by decide)
  · exact m13_11_1_5_12

theorem m13_11_1_6_0 : go 13 7 9 [11, 1, 6, 0] = true := by decide +kernel
theorem m13_11_1_6_2 : go 13 7 9 [11, 1, 6, 2] = true := by decide +kernel
theorem m13_11_1_6_4 : go 13 7 9 [11, 1, 6, 4] = true := by decide +kernel
theorem m13_11_1_6_9 : go 13 7 9 [11, 1, 6, 9] = true := by decide +kernel
theorem m13_11_1_6_10 : go 13 7 9 [11, 1, 6, 10] = true := by decide +kernel
theorem m13_11_1_6_12 : go 13 7 9 [11, 1, 6, 12] = true := by decide +kernel

theorem m13_11_1_6 : go 13 7 10 [11, 1, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_6_0
  · exact absurd hs (by decide)
  · exact m13_11_1_6_2
  · exact absurd hs (by decide)
  · exact m13_11_1_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_6_9
  · exact m13_11_1_6_10
  · exact absurd hs (by decide)
  · exact m13_11_1_6_12

theorem m13_11_1_7_0 : go 13 7 9 [11, 1, 7, 0] = true := by decide +kernel
theorem m13_11_1_7_2 : go 13 7 9 [11, 1, 7, 2] = true := by decide +kernel
theorem m13_11_1_7_4 : go 13 7 9 [11, 1, 7, 4] = true := by decide +kernel
theorem m13_11_1_7_5 : go 13 7 9 [11, 1, 7, 5] = true := by decide +kernel
theorem m13_11_1_7_9 : go 13 7 9 [11, 1, 7, 9] = true := by decide +kernel
theorem m13_11_1_7_10 : go 13 7 9 [11, 1, 7, 10] = true := by decide +kernel
theorem m13_11_1_7_12 : go 13 7 9 [11, 1, 7, 12] = true := by decide +kernel

theorem m13_11_1_7 : go 13 7 10 [11, 1, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_7_0
  · exact absurd hs (by decide)
  · exact m13_11_1_7_2
  · exact absurd hs (by decide)
  · exact m13_11_1_7_4
  · exact m13_11_1_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_7_9
  · exact m13_11_1_7_10
  · exact absurd hs (by decide)
  · exact m13_11_1_7_12

theorem m13_11_1_8_0 : go 13 7 9 [11, 1, 8, 0] = true := by decide +kernel
theorem m13_11_1_8_2 : go 13 7 9 [11, 1, 8, 2] = true := by decide +kernel
theorem m13_11_1_8_4 : go 13 7 9 [11, 1, 8, 4] = true := by decide +kernel
theorem m13_11_1_8_5 : go 13 7 9 [11, 1, 8, 5] = true := by decide +kernel
theorem m13_11_1_8_6 : go 13 7 9 [11, 1, 8, 6] = true := by decide +kernel
theorem m13_11_1_8_10 : go 13 7 9 [11, 1, 8, 10] = true := by decide +kernel
theorem m13_11_1_8_12 : go 13 7 9 [11, 1, 8, 12] = true := by decide +kernel

theorem m13_11_1_8 : go 13 7 10 [11, 1, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_8_0
  · exact absurd hs (by decide)
  · exact m13_11_1_8_2
  · exact absurd hs (by decide)
  · exact m13_11_1_8_4
  · exact m13_11_1_8_5
  · exact m13_11_1_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_8_10
  · exact absurd hs (by decide)
  · exact m13_11_1_8_12

theorem m13_11_1_10_0 : go 13 7 9 [11, 1, 10, 0] = true := by decide +kernel
theorem m13_11_1_10_2 : go 13 7 9 [11, 1, 10, 2] = true := by decide +kernel
theorem m13_11_1_10_4 : go 13 7 9 [11, 1, 10, 4] = true := by decide +kernel
theorem m13_11_1_10_5 : go 13 7 9 [11, 1, 10, 5] = true := by decide +kernel
theorem m13_11_1_10_6 : go 13 7 9 [11, 1, 10, 6] = true := by decide +kernel
theorem m13_11_1_10_7 : go 13 7 9 [11, 1, 10, 7] = true := by decide +kernel
theorem m13_11_1_10_12 : go 13 7 9 [11, 1, 10, 12] = true := by decide +kernel

theorem m13_11_1_10 : go 13 7 10 [11, 1, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_10_0
  · exact absurd hs (by decide)
  · exact m13_11_1_10_2
  · exact absurd hs (by decide)
  · exact m13_11_1_10_4
  · exact m13_11_1_10_5
  · exact m13_11_1_10_6
  · exact m13_11_1_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_10_12

theorem m13_11_1_12_0 : go 13 7 9 [11, 1, 12, 0] = true := by decide +kernel
theorem m13_11_1_12_2 : go 13 7 9 [11, 1, 12, 2] = true := by decide +kernel
theorem m13_11_1_12_4 : go 13 7 9 [11, 1, 12, 4] = true := by decide +kernel
theorem m13_11_1_12_5 : go 13 7 9 [11, 1, 12, 5] = true := by decide +kernel
theorem m13_11_1_12_6 : go 13 7 9 [11, 1, 12, 6] = true := by decide +kernel
theorem m13_11_1_12_7 : go 13 7 9 [11, 1, 12, 7] = true := by decide +kernel
theorem m13_11_1_12_9 : go 13 7 9 [11, 1, 12, 9] = true := by decide +kernel
theorem m13_11_1_12_10 : go 13 7 9 [11, 1, 12, 10] = true := by decide +kernel

theorem m13_11_1_12 : go 13 7 10 [11, 1, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_1_12_0
  · exact absurd hs (by decide)
  · exact m13_11_1_12_2
  · exact absurd hs (by decide)
  · exact m13_11_1_12_4
  · exact m13_11_1_12_5
  · exact m13_11_1_12_6
  · exact m13_11_1_12_7
  · exact absurd hs (by decide)
  · exact m13_11_1_12_9
  · exact m13_11_1_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_11_1 : go 13 7 11 [11, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_1_3
  · exact m13_11_1_4
  · exact m13_11_1_5
  · exact m13_11_1_6
  · exact m13_11_1_7
  · exact m13_11_1_8
  · exact absurd hs (by decide)
  · exact m13_11_1_10
  · exact absurd hs (by decide)
  · exact m13_11_1_12

end Misses
