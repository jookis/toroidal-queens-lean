import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [0, 3]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_0_3_1_4 : go 13 7 9 [0, 3, 1, 4] = true := by decide +kernel
theorem m13_0_3_1_6 : go 13 7 9 [0, 3, 1, 6] = true := by decide +kernel
theorem m13_0_3_1_7 : go 13 7 9 [0, 3, 1, 7] = true := by decide +kernel
theorem m13_0_3_1_8 : go 13 7 9 [0, 3, 1, 8] = true := by decide +kernel
theorem m13_0_3_1_9 : go 13 7 9 [0, 3, 1, 9] = true := by decide +kernel
theorem m13_0_3_1_10 : go 13 7 9 [0, 3, 1, 10] = true := by decide +kernel
theorem m13_0_3_1_11 : go 13 7 9 [0, 3, 1, 11] = true := by decide +kernel
theorem m13_0_3_1_12 : go 13 7 9 [0, 3, 1, 12] = true := by decide +kernel

theorem m13_0_3_1 : go 13 7 10 [0, 3, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_1_4
  · exact absurd hs (by decide)
  · exact m13_0_3_1_6
  · exact m13_0_3_1_7
  · exact m13_0_3_1_8
  · exact m13_0_3_1_9
  · exact m13_0_3_1_10
  · exact m13_0_3_1_11
  · exact m13_0_3_1_12

theorem m13_0_3_5_2 : go 13 7 9 [0, 3, 5, 2] = true := by decide +kernel
theorem m13_0_3_5_7 : go 13 7 9 [0, 3, 5, 7] = true := by decide +kernel
theorem m13_0_3_5_8 : go 13 7 9 [0, 3, 5, 8] = true := by decide +kernel
theorem m13_0_3_5_9 : go 13 7 9 [0, 3, 5, 9] = true := by decide +kernel
theorem m13_0_3_5_10 : go 13 7 9 [0, 3, 5, 10] = true := by decide +kernel
theorem m13_0_3_5_11 : go 13 7 9 [0, 3, 5, 11] = true := by decide +kernel
theorem m13_0_3_5_12 : go 13 7 9 [0, 3, 5, 12] = true := by decide +kernel

theorem m13_0_3_5 : go 13 7 10 [0, 3, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_5_7
  · exact m13_0_3_5_8
  · exact m13_0_3_5_9
  · exact m13_0_3_5_10
  · exact m13_0_3_5_11
  · exact m13_0_3_5_12

theorem m13_0_3_6_2 : go 13 7 9 [0, 3, 6, 2] = true := by decide +kernel
theorem m13_0_3_6_4 : go 13 7 9 [0, 3, 6, 4] = true := by decide +kernel
theorem m13_0_3_6_8 : go 13 7 9 [0, 3, 6, 8] = true := by decide +kernel
theorem m13_0_3_6_9 : go 13 7 9 [0, 3, 6, 9] = true := by decide +kernel
theorem m13_0_3_6_10 : go 13 7 9 [0, 3, 6, 10] = true := by decide +kernel
theorem m13_0_3_6_11 : go 13 7 9 [0, 3, 6, 11] = true := by decide +kernel
theorem m13_0_3_6_12 : go 13 7 9 [0, 3, 6, 12] = true := by decide +kernel

theorem m13_0_3_6 : go 13 7 10 [0, 3, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_6_2
  · exact absurd hs (by decide)
  · exact m13_0_3_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_6_8
  · exact m13_0_3_6_9
  · exact m13_0_3_6_10
  · exact m13_0_3_6_11
  · exact m13_0_3_6_12

theorem m13_0_3_7_2 : go 13 7 9 [0, 3, 7, 2] = true := by decide +kernel
theorem m13_0_3_7_4 : go 13 7 9 [0, 3, 7, 4] = true := by decide +kernel
theorem m13_0_3_7_9 : go 13 7 9 [0, 3, 7, 9] = true := by decide +kernel
theorem m13_0_3_7_10 : go 13 7 9 [0, 3, 7, 10] = true := by decide +kernel
theorem m13_0_3_7_11 : go 13 7 9 [0, 3, 7, 11] = true := by decide +kernel
theorem m13_0_3_7_12 : go 13 7 9 [0, 3, 7, 12] = true := by decide +kernel

theorem m13_0_3_7 : go 13 7 10 [0, 3, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_7_2
  · exact absurd hs (by decide)
  · exact m13_0_3_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_7_9
  · exact m13_0_3_7_10
  · exact m13_0_3_7_11
  · exact m13_0_3_7_12

theorem m13_0_3_8_2 : go 13 7 9 [0, 3, 8, 2] = true := by decide +kernel
theorem m13_0_3_8_4 : go 13 7 9 [0, 3, 8, 4] = true := by decide +kernel
theorem m13_0_3_8_6 : go 13 7 9 [0, 3, 8, 6] = true := by decide +kernel
theorem m13_0_3_8_10 : go 13 7 9 [0, 3, 8, 10] = true := by decide +kernel
theorem m13_0_3_8_11 : go 13 7 9 [0, 3, 8, 11] = true := by decide +kernel
theorem m13_0_3_8_12 : go 13 7 9 [0, 3, 8, 12] = true := by decide +kernel

theorem m13_0_3_8 : go 13 7 10 [0, 3, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_8_2
  · exact absurd hs (by decide)
  · exact m13_0_3_8_4
  · exact absurd hs (by decide)
  · exact m13_0_3_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_8_10
  · exact m13_0_3_8_11
  · exact m13_0_3_8_12

theorem m13_0_3_9_2 : go 13 7 9 [0, 3, 9, 2] = true := by decide +kernel
theorem m13_0_3_9_4 : go 13 7 9 [0, 3, 9, 4] = true := by decide +kernel
theorem m13_0_3_9_6 : go 13 7 9 [0, 3, 9, 6] = true := by decide +kernel
theorem m13_0_3_9_7 : go 13 7 9 [0, 3, 9, 7] = true := by decide +kernel
theorem m13_0_3_9_11 : go 13 7 9 [0, 3, 9, 11] = true := by decide +kernel
theorem m13_0_3_9_12 : go 13 7 9 [0, 3, 9, 12] = true := by decide +kernel

theorem m13_0_3_9 : go 13 7 10 [0, 3, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_9_2
  · exact absurd hs (by decide)
  · exact m13_0_3_9_4
  · exact absurd hs (by decide)
  · exact m13_0_3_9_6
  · exact m13_0_3_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_9_11
  · exact m13_0_3_9_12

theorem m13_0_3_10_2 : go 13 7 9 [0, 3, 10, 2] = true := by decide +kernel
theorem m13_0_3_10_4 : go 13 7 9 [0, 3, 10, 4] = true := by decide +kernel
theorem m13_0_3_10_6 : go 13 7 9 [0, 3, 10, 6] = true := by decide +kernel
theorem m13_0_3_10_7 : go 13 7 9 [0, 3, 10, 7] = true := by decide +kernel
theorem m13_0_3_10_8 : go 13 7 9 [0, 3, 10, 8] = true := by decide +kernel
theorem m13_0_3_10_12 : go 13 7 9 [0, 3, 10, 12] = true := by decide +kernel

theorem m13_0_3_10 : go 13 7 10 [0, 3, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_10_2
  · exact absurd hs (by decide)
  · exact m13_0_3_10_4
  · exact absurd hs (by decide)
  · exact m13_0_3_10_6
  · exact m13_0_3_10_7
  · exact m13_0_3_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_10_12

theorem m13_0_3_11_2 : go 13 7 9 [0, 3, 11, 2] = true := by decide +kernel
theorem m13_0_3_11_4 : go 13 7 9 [0, 3, 11, 4] = true := by decide +kernel
theorem m13_0_3_11_6 : go 13 7 9 [0, 3, 11, 6] = true := by decide +kernel
theorem m13_0_3_11_7 : go 13 7 9 [0, 3, 11, 7] = true := by decide +kernel
theorem m13_0_3_11_8 : go 13 7 9 [0, 3, 11, 8] = true := by decide +kernel
theorem m13_0_3_11_9 : go 13 7 9 [0, 3, 11, 9] = true := by decide +kernel

theorem m13_0_3_11 : go 13 7 10 [0, 3, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_11_2
  · exact absurd hs (by decide)
  · exact m13_0_3_11_4
  · exact absurd hs (by decide)
  · exact m13_0_3_11_6
  · exact m13_0_3_11_7
  · exact m13_0_3_11_8
  · exact m13_0_3_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_0_3_12_2 : go 13 7 9 [0, 3, 12, 2] = true := by decide +kernel
theorem m13_0_3_12_4 : go 13 7 9 [0, 3, 12, 4] = true := by decide +kernel
theorem m13_0_3_12_6 : go 13 7 9 [0, 3, 12, 6] = true := by decide +kernel
theorem m13_0_3_12_7 : go 13 7 9 [0, 3, 12, 7] = true := by decide +kernel
theorem m13_0_3_12_8 : go 13 7 9 [0, 3, 12, 8] = true := by decide +kernel
theorem m13_0_3_12_9 : go 13 7 9 [0, 3, 12, 9] = true := by decide +kernel
theorem m13_0_3_12_10 : go 13 7 9 [0, 3, 12, 10] = true := by decide +kernel

theorem m13_0_3_12 : go 13 7 10 [0, 3, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_12_2
  · exact absurd hs (by decide)
  · exact m13_0_3_12_4
  · exact absurd hs (by decide)
  · exact m13_0_3_12_6
  · exact m13_0_3_12_7
  · exact m13_0_3_12_8
  · exact m13_0_3_12_9
  · exact m13_0_3_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_0_3 : go 13 7 11 [0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_3_5
  · exact m13_0_3_6
  · exact m13_0_3_7
  · exact m13_0_3_8
  · exact m13_0_3_9
  · exact m13_0_3_10
  · exact m13_0_3_11
  · exact m13_0_3_12

end Misses
