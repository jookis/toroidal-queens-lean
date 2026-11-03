import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [0, 2]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_0_2_4_1 : go 13 7 9 [0, 2, 4, 1] = true := by decide +kernel
theorem m13_0_2_4_6 : go 13 7 9 [0, 2, 4, 6] = true := by decide +kernel
theorem m13_0_2_4_7 : go 13 7 9 [0, 2, 4, 7] = true := by decide +kernel
theorem m13_0_2_4_8 : go 13 7 9 [0, 2, 4, 8] = true := by decide +kernel
theorem m13_0_2_4_9 : go 13 7 9 [0, 2, 4, 9] = true := by decide +kernel
theorem m13_0_2_4_10 : go 13 7 9 [0, 2, 4, 10] = true := by decide +kernel
theorem m13_0_2_4_11 : go 13 7 9 [0, 2, 4, 11] = true := by decide +kernel
theorem m13_0_2_4_12 : go 13 7 9 [0, 2, 4, 12] = true := by decide +kernel

theorem m13_0_2_4 : go 13 7 10 [0, 2, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_4_6
  · exact m13_0_2_4_7
  · exact m13_0_2_4_8
  · exact m13_0_2_4_9
  · exact m13_0_2_4_10
  · exact m13_0_2_4_11
  · exact m13_0_2_4_12

theorem m13_0_2_5_1 : go 13 7 9 [0, 2, 5, 1] = true := by decide +kernel
theorem m13_0_2_5_7 : go 13 7 9 [0, 2, 5, 7] = true := by decide +kernel
theorem m13_0_2_5_8 : go 13 7 9 [0, 2, 5, 8] = true := by decide +kernel
theorem m13_0_2_5_9 : go 13 7 9 [0, 2, 5, 9] = true := by decide +kernel
theorem m13_0_2_5_10 : go 13 7 9 [0, 2, 5, 10] = true := by decide +kernel
theorem m13_0_2_5_11 : go 13 7 9 [0, 2, 5, 11] = true := by decide +kernel
theorem m13_0_2_5_12 : go 13 7 9 [0, 2, 5, 12] = true := by decide +kernel

theorem m13_0_2_5 : go 13 7 10 [0, 2, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_5_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_5_7
  · exact m13_0_2_5_8
  · exact m13_0_2_5_9
  · exact m13_0_2_5_10
  · exact m13_0_2_5_11
  · exact m13_0_2_5_12

theorem m13_0_2_6_1 : go 13 7 9 [0, 2, 6, 1] = true := by decide +kernel
theorem m13_0_2_6_8 : go 13 7 9 [0, 2, 6, 8] = true := by decide +kernel
theorem m13_0_2_6_9 : go 13 7 9 [0, 2, 6, 9] = true := by decide +kernel
theorem m13_0_2_6_10 : go 13 7 9 [0, 2, 6, 10] = true := by decide +kernel
theorem m13_0_2_6_11 : go 13 7 9 [0, 2, 6, 11] = true := by decide +kernel
theorem m13_0_2_6_12 : go 13 7 9 [0, 2, 6, 12] = true := by decide +kernel

theorem m13_0_2_6 : go 13 7 10 [0, 2, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_6_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_6_8
  · exact m13_0_2_6_9
  · exact m13_0_2_6_10
  · exact m13_0_2_6_11
  · exact m13_0_2_6_12

theorem m13_0_2_7_1 : go 13 7 9 [0, 2, 7, 1] = true := by decide +kernel
theorem m13_0_2_7_5 : go 13 7 9 [0, 2, 7, 5] = true := by decide +kernel
theorem m13_0_2_7_9 : go 13 7 9 [0, 2, 7, 9] = true := by decide +kernel
theorem m13_0_2_7_10 : go 13 7 9 [0, 2, 7, 10] = true := by decide +kernel
theorem m13_0_2_7_11 : go 13 7 9 [0, 2, 7, 11] = true := by decide +kernel
theorem m13_0_2_7_12 : go 13 7 9 [0, 2, 7, 12] = true := by decide +kernel

theorem m13_0_2_7 : go 13 7 10 [0, 2, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_7_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_7_9
  · exact m13_0_2_7_10
  · exact m13_0_2_7_11
  · exact m13_0_2_7_12

theorem m13_0_2_8_1 : go 13 7 9 [0, 2, 8, 1] = true := by decide +kernel
theorem m13_0_2_8_5 : go 13 7 9 [0, 2, 8, 5] = true := by decide +kernel
theorem m13_0_2_8_6 : go 13 7 9 [0, 2, 8, 6] = true := by decide +kernel
theorem m13_0_2_8_10 : go 13 7 9 [0, 2, 8, 10] = true := by decide +kernel
theorem m13_0_2_8_11 : go 13 7 9 [0, 2, 8, 11] = true := by decide +kernel
theorem m13_0_2_8_12 : go 13 7 9 [0, 2, 8, 12] = true := by decide +kernel

theorem m13_0_2_8 : go 13 7 10 [0, 2, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_8_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_8_5
  · exact m13_0_2_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_8_10
  · exact m13_0_2_8_11
  · exact m13_0_2_8_12

theorem m13_0_2_9_1 : go 13 7 9 [0, 2, 9, 1] = true := by decide +kernel
theorem m13_0_2_9_5 : go 13 7 9 [0, 2, 9, 5] = true := by decide +kernel
theorem m13_0_2_9_6 : go 13 7 9 [0, 2, 9, 6] = true := by decide +kernel
theorem m13_0_2_9_7 : go 13 7 9 [0, 2, 9, 7] = true := by decide +kernel
theorem m13_0_2_9_11 : go 13 7 9 [0, 2, 9, 11] = true := by decide +kernel
theorem m13_0_2_9_12 : go 13 7 9 [0, 2, 9, 12] = true := by decide +kernel

theorem m13_0_2_9 : go 13 7 10 [0, 2, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_9_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_9_5
  · exact m13_0_2_9_6
  · exact m13_0_2_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_9_11
  · exact m13_0_2_9_12

theorem m13_0_2_10_1 : go 13 7 9 [0, 2, 10, 1] = true := by decide +kernel
theorem m13_0_2_10_5 : go 13 7 9 [0, 2, 10, 5] = true := by decide +kernel
theorem m13_0_2_10_6 : go 13 7 9 [0, 2, 10, 6] = true := by decide +kernel
theorem m13_0_2_10_7 : go 13 7 9 [0, 2, 10, 7] = true := by decide +kernel
theorem m13_0_2_10_8 : go 13 7 9 [0, 2, 10, 8] = true := by decide +kernel
theorem m13_0_2_10_12 : go 13 7 9 [0, 2, 10, 12] = true := by decide +kernel

theorem m13_0_2_10 : go 13 7 10 [0, 2, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_10_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_10_5
  · exact m13_0_2_10_6
  · exact m13_0_2_10_7
  · exact m13_0_2_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_10_12

theorem m13_0_2_11_1 : go 13 7 9 [0, 2, 11, 1] = true := by decide +kernel
theorem m13_0_2_11_5 : go 13 7 9 [0, 2, 11, 5] = true := by decide +kernel
theorem m13_0_2_11_6 : go 13 7 9 [0, 2, 11, 6] = true := by decide +kernel
theorem m13_0_2_11_7 : go 13 7 9 [0, 2, 11, 7] = true := by decide +kernel
theorem m13_0_2_11_8 : go 13 7 9 [0, 2, 11, 8] = true := by decide +kernel
theorem m13_0_2_11_9 : go 13 7 9 [0, 2, 11, 9] = true := by decide +kernel

theorem m13_0_2_11 : go 13 7 10 [0, 2, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_11_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_11_5
  · exact m13_0_2_11_6
  · exact m13_0_2_11_7
  · exact m13_0_2_11_8
  · exact m13_0_2_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_0_2_12_1 : go 13 7 9 [0, 2, 12, 1] = true := by decide +kernel
theorem m13_0_2_12_5 : go 13 7 9 [0, 2, 12, 5] = true := by decide +kernel
theorem m13_0_2_12_6 : go 13 7 9 [0, 2, 12, 6] = true := by decide +kernel
theorem m13_0_2_12_7 : go 13 7 9 [0, 2, 12, 7] = true := by decide +kernel
theorem m13_0_2_12_8 : go 13 7 9 [0, 2, 12, 8] = true := by decide +kernel
theorem m13_0_2_12_9 : go 13 7 9 [0, 2, 12, 9] = true := by decide +kernel
theorem m13_0_2_12_10 : go 13 7 9 [0, 2, 12, 10] = true := by decide +kernel

theorem m13_0_2_12 : go 13 7 10 [0, 2, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_0_2_12_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_12_5
  · exact m13_0_2_12_6
  · exact m13_0_2_12_7
  · exact m13_0_2_12_8
  · exact m13_0_2_12_9
  · exact m13_0_2_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_0_2 : go 13 7 11 [0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_0_2_4
  · exact m13_0_2_5
  · exact m13_0_2_6
  · exact m13_0_2_7
  · exact m13_0_2_8
  · exact m13_0_2_9
  · exact m13_0_2_10
  · exact m13_0_2_11
  · exact m13_0_2_12

end Misses
