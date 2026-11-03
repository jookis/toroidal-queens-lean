import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 8]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_8_1_3 : go 13 7 9 [2, 8, 1, 3] = true := by decide +kernel
theorem m13_2_8_1_4 : go 13 7 9 [2, 8, 1, 4] = true := by decide +kernel
theorem m13_2_8_1_7 : go 13 7 9 [2, 8, 1, 7] = true := by decide +kernel
theorem m13_2_8_1_9 : go 13 7 9 [2, 8, 1, 9] = true := by decide +kernel
theorem m13_2_8_1_11 : go 13 7 9 [2, 8, 1, 11] = true := by decide +kernel
theorem m13_2_8_1_12 : go 13 7 9 [2, 8, 1, 12] = true := by decide +kernel

theorem m13_2_8_1 : go 13 7 10 [2, 8, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_1_3
  · exact m13_2_8_1_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_1_7
  · exact absurd hs (by decide)
  · exact m13_2_8_1_9
  · exact absurd hs (by decide)
  · exact m13_2_8_1_11
  · exact m13_2_8_1_12

theorem m13_2_8_3_0 : go 13 7 9 [2, 8, 3, 0] = true := by decide +kernel
theorem m13_2_8_3_1 : go 13 7 9 [2, 8, 3, 1] = true := by decide +kernel
theorem m13_2_8_3_7 : go 13 7 9 [2, 8, 3, 7] = true := by decide +kernel
theorem m13_2_8_3_9 : go 13 7 9 [2, 8, 3, 9] = true := by decide +kernel
theorem m13_2_8_3_11 : go 13 7 9 [2, 8, 3, 11] = true := by decide +kernel
theorem m13_2_8_3_12 : go 13 7 9 [2, 8, 3, 12] = true := by decide +kernel

theorem m13_2_8_3 : go 13 7 10 [2, 8, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_8_3_0
  · exact m13_2_8_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_3_7
  · exact absurd hs (by decide)
  · exact m13_2_8_3_9
  · exact absurd hs (by decide)
  · exact m13_2_8_3_11
  · exact m13_2_8_3_12

theorem m13_2_8_5_0 : go 13 7 9 [2, 8, 5, 0] = true := by decide +kernel
theorem m13_2_8_5_1 : go 13 7 9 [2, 8, 5, 1] = true := by decide +kernel
theorem m13_2_8_5_3 : go 13 7 9 [2, 8, 5, 3] = true := by decide +kernel
theorem m13_2_8_5_7 : go 13 7 9 [2, 8, 5, 7] = true := by decide +kernel
theorem m13_2_8_5_9 : go 13 7 9 [2, 8, 5, 9] = true := by decide +kernel
theorem m13_2_8_5_11 : go 13 7 9 [2, 8, 5, 11] = true := by decide +kernel
theorem m13_2_8_5_12 : go 13 7 9 [2, 8, 5, 12] = true := by decide +kernel

theorem m13_2_8_5 : go 13 7 10 [2, 8, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_8_5_0
  · exact m13_2_8_5_1
  · exact absurd hs (by decide)
  · exact m13_2_8_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_5_7
  · exact absurd hs (by decide)
  · exact m13_2_8_5_9
  · exact absurd hs (by decide)
  · exact m13_2_8_5_11
  · exact m13_2_8_5_12

theorem m13_2_8_6_0 : go 13 7 9 [2, 8, 6, 0] = true := by decide +kernel
theorem m13_2_8_6_1 : go 13 7 9 [2, 8, 6, 1] = true := by decide +kernel
theorem m13_2_8_6_3 : go 13 7 9 [2, 8, 6, 3] = true := by decide +kernel
theorem m13_2_8_6_4 : go 13 7 9 [2, 8, 6, 4] = true := by decide +kernel
theorem m13_2_8_6_9 : go 13 7 9 [2, 8, 6, 9] = true := by decide +kernel
theorem m13_2_8_6_11 : go 13 7 9 [2, 8, 6, 11] = true := by decide +kernel
theorem m13_2_8_6_12 : go 13 7 9 [2, 8, 6, 12] = true := by decide +kernel

theorem m13_2_8_6 : go 13 7 10 [2, 8, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_8_6_0
  · exact m13_2_8_6_1
  · exact absurd hs (by decide)
  · exact m13_2_8_6_3
  · exact m13_2_8_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_6_9
  · exact absurd hs (by decide)
  · exact m13_2_8_6_11
  · exact m13_2_8_6_12

theorem m13_2_8_10_0 : go 13 7 9 [2, 8, 10, 0] = true := by decide +kernel
theorem m13_2_8_10_1 : go 13 7 9 [2, 8, 10, 1] = true := by decide +kernel
theorem m13_2_8_10_3 : go 13 7 9 [2, 8, 10, 3] = true := by decide +kernel
theorem m13_2_8_10_4 : go 13 7 9 [2, 8, 10, 4] = true := by decide +kernel
theorem m13_2_8_10_7 : go 13 7 9 [2, 8, 10, 7] = true := by decide +kernel
theorem m13_2_8_10_12 : go 13 7 9 [2, 8, 10, 12] = true := by decide +kernel

theorem m13_2_8_10 : go 13 7 10 [2, 8, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_8_10_0
  · exact m13_2_8_10_1
  · exact absurd hs (by decide)
  · exact m13_2_8_10_3
  · exact m13_2_8_10_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_10_12

theorem m13_2_8_11_0 : go 13 7 9 [2, 8, 11, 0] = true := by decide +kernel
theorem m13_2_8_11_1 : go 13 7 9 [2, 8, 11, 1] = true := by decide +kernel
theorem m13_2_8_11_3 : go 13 7 9 [2, 8, 11, 3] = true := by decide +kernel
theorem m13_2_8_11_4 : go 13 7 9 [2, 8, 11, 4] = true := by decide +kernel
theorem m13_2_8_11_7 : go 13 7 9 [2, 8, 11, 7] = true := by decide +kernel
theorem m13_2_8_11_9 : go 13 7 9 [2, 8, 11, 9] = true := by decide +kernel

theorem m13_2_8_11 : go 13 7 10 [2, 8, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_8_11_0
  · exact m13_2_8_11_1
  · exact absurd hs (by decide)
  · exact m13_2_8_11_3
  · exact m13_2_8_11_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_11_7
  · exact absurd hs (by decide)
  · exact m13_2_8_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_8_12_0 : go 13 7 9 [2, 8, 12, 0] = true := by decide +kernel
theorem m13_2_8_12_1 : go 13 7 9 [2, 8, 12, 1] = true := by decide +kernel
theorem m13_2_8_12_3 : go 13 7 9 [2, 8, 12, 3] = true := by decide +kernel
theorem m13_2_8_12_4 : go 13 7 9 [2, 8, 12, 4] = true := by decide +kernel
theorem m13_2_8_12_7 : go 13 7 9 [2, 8, 12, 7] = true := by decide +kernel
theorem m13_2_8_12_9 : go 13 7 9 [2, 8, 12, 9] = true := by decide +kernel

theorem m13_2_8_12 : go 13 7 10 [2, 8, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_8_12_0
  · exact m13_2_8_12_1
  · exact absurd hs (by decide)
  · exact m13_2_8_12_3
  · exact m13_2_8_12_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_12_7
  · exact absurd hs (by decide)
  · exact m13_2_8_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_8 : go 13 7 11 [2, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_8_1
  · exact absurd hs (by decide)
  · exact m13_2_8_3
  · exact absurd hs (by decide)
  · exact m13_2_8_5
  · exact m13_2_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_8_10
  · exact m13_2_8_11
  · exact m13_2_8_12

end Misses
