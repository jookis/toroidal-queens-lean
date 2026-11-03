import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_0_2_4 : go 13 7 9 [3, 0, 2, 4] = true := by decide +kernel
theorem m13_3_0_2_5 : go 13 7 9 [3, 0, 2, 5] = true := by decide +kernel
theorem m13_3_0_2_7 : go 13 7 9 [3, 0, 2, 7] = true := by decide +kernel
theorem m13_3_0_2_8 : go 13 7 9 [3, 0, 2, 8] = true := by decide +kernel
theorem m13_3_0_2_9 : go 13 7 9 [3, 0, 2, 9] = true := by decide +kernel
theorem m13_3_0_2_10 : go 13 7 9 [3, 0, 2, 10] = true := by decide +kernel
theorem m13_3_0_2_11 : go 13 7 9 [3, 0, 2, 11] = true := by decide +kernel
theorem m13_3_0_2_12 : go 13 7 9 [3, 0, 2, 12] = true := by decide +kernel

theorem m13_3_0_2 : go 13 7 10 [3, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_2_4
  · exact m13_3_0_2_5
  · exact absurd hs (by decide)
  · exact m13_3_0_2_7
  · exact m13_3_0_2_8
  · exact m13_3_0_2_9
  · exact m13_3_0_2_10
  · exact m13_3_0_2_11
  · exact m13_3_0_2_12

theorem m13_3_0_4_1 : go 13 7 9 [3, 0, 4, 1] = true := by decide +kernel
theorem m13_3_0_4_7 : go 13 7 9 [3, 0, 4, 7] = true := by decide +kernel
theorem m13_3_0_4_8 : go 13 7 9 [3, 0, 4, 8] = true := by decide +kernel
theorem m13_3_0_4_9 : go 13 7 9 [3, 0, 4, 9] = true := by decide +kernel
theorem m13_3_0_4_10 : go 13 7 9 [3, 0, 4, 10] = true := by decide +kernel
theorem m13_3_0_4_11 : go 13 7 9 [3, 0, 4, 11] = true := by decide +kernel
theorem m13_3_0_4_12 : go 13 7 9 [3, 0, 4, 12] = true := by decide +kernel

theorem m13_3_0_4 : go 13 7 10 [3, 0, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_4_7
  · exact m13_3_0_4_8
  · exact m13_3_0_4_9
  · exact m13_3_0_4_10
  · exact m13_3_0_4_11
  · exact m13_3_0_4_12

theorem m13_3_0_6_1 : go 13 7 9 [3, 0, 6, 1] = true := by decide +kernel
theorem m13_3_0_6_4 : go 13 7 9 [3, 0, 6, 4] = true := by decide +kernel
theorem m13_3_0_6_8 : go 13 7 9 [3, 0, 6, 8] = true := by decide +kernel
theorem m13_3_0_6_9 : go 13 7 9 [3, 0, 6, 9] = true := by decide +kernel
theorem m13_3_0_6_10 : go 13 7 9 [3, 0, 6, 10] = true := by decide +kernel
theorem m13_3_0_6_11 : go 13 7 9 [3, 0, 6, 11] = true := by decide +kernel
theorem m13_3_0_6_12 : go 13 7 9 [3, 0, 6, 12] = true := by decide +kernel

theorem m13_3_0_6 : go 13 7 10 [3, 0, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_6_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_6_8
  · exact m13_3_0_6_9
  · exact m13_3_0_6_10
  · exact m13_3_0_6_11
  · exact m13_3_0_6_12

theorem m13_3_0_7_1 : go 13 7 9 [3, 0, 7, 1] = true := by decide +kernel
theorem m13_3_0_7_4 : go 13 7 9 [3, 0, 7, 4] = true := by decide +kernel
theorem m13_3_0_7_5 : go 13 7 9 [3, 0, 7, 5] = true := by decide +kernel
theorem m13_3_0_7_9 : go 13 7 9 [3, 0, 7, 9] = true := by decide +kernel
theorem m13_3_0_7_10 : go 13 7 9 [3, 0, 7, 10] = true := by decide +kernel
theorem m13_3_0_7_11 : go 13 7 9 [3, 0, 7, 11] = true := by decide +kernel
theorem m13_3_0_7_12 : go 13 7 9 [3, 0, 7, 12] = true := by decide +kernel

theorem m13_3_0_7 : go 13 7 10 [3, 0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_7_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_7_4
  · exact m13_3_0_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_7_9
  · exact m13_3_0_7_10
  · exact m13_3_0_7_11
  · exact m13_3_0_7_12

theorem m13_3_0_8_1 : go 13 7 9 [3, 0, 8, 1] = true := by decide +kernel
theorem m13_3_0_8_4 : go 13 7 9 [3, 0, 8, 4] = true := by decide +kernel
theorem m13_3_0_8_5 : go 13 7 9 [3, 0, 8, 5] = true := by decide +kernel
theorem m13_3_0_8_10 : go 13 7 9 [3, 0, 8, 10] = true := by decide +kernel
theorem m13_3_0_8_11 : go 13 7 9 [3, 0, 8, 11] = true := by decide +kernel
theorem m13_3_0_8_12 : go 13 7 9 [3, 0, 8, 12] = true := by decide +kernel

theorem m13_3_0_8 : go 13 7 10 [3, 0, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_8_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_8_4
  · exact m13_3_0_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_8_10
  · exact m13_3_0_8_11
  · exact m13_3_0_8_12

theorem m13_3_0_9_1 : go 13 7 9 [3, 0, 9, 1] = true := by decide +kernel
theorem m13_3_0_9_4 : go 13 7 9 [3, 0, 9, 4] = true := by decide +kernel
theorem m13_3_0_9_5 : go 13 7 9 [3, 0, 9, 5] = true := by decide +kernel
theorem m13_3_0_9_7 : go 13 7 9 [3, 0, 9, 7] = true := by decide +kernel
theorem m13_3_0_9_11 : go 13 7 9 [3, 0, 9, 11] = true := by decide +kernel
theorem m13_3_0_9_12 : go 13 7 9 [3, 0, 9, 12] = true := by decide +kernel

theorem m13_3_0_9 : go 13 7 10 [3, 0, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_9_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_9_4
  · exact m13_3_0_9_5
  · exact absurd hs (by decide)
  · exact m13_3_0_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_9_11
  · exact m13_3_0_9_12

theorem m13_3_0_10_1 : go 13 7 9 [3, 0, 10, 1] = true := by decide +kernel
theorem m13_3_0_10_4 : go 13 7 9 [3, 0, 10, 4] = true := by decide +kernel
theorem m13_3_0_10_5 : go 13 7 9 [3, 0, 10, 5] = true := by decide +kernel
theorem m13_3_0_10_7 : go 13 7 9 [3, 0, 10, 7] = true := by decide +kernel
theorem m13_3_0_10_8 : go 13 7 9 [3, 0, 10, 8] = true := by decide +kernel
theorem m13_3_0_10_12 : go 13 7 9 [3, 0, 10, 12] = true := by decide +kernel

theorem m13_3_0_10 : go 13 7 10 [3, 0, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_10_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_10_4
  · exact m13_3_0_10_5
  · exact absurd hs (by decide)
  · exact m13_3_0_10_7
  · exact m13_3_0_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_10_12

theorem m13_3_0_11_1 : go 13 7 9 [3, 0, 11, 1] = true := by decide +kernel
theorem m13_3_0_11_4 : go 13 7 9 [3, 0, 11, 4] = true := by decide +kernel
theorem m13_3_0_11_5 : go 13 7 9 [3, 0, 11, 5] = true := by decide +kernel
theorem m13_3_0_11_7 : go 13 7 9 [3, 0, 11, 7] = true := by decide +kernel
theorem m13_3_0_11_8 : go 13 7 9 [3, 0, 11, 8] = true := by decide +kernel
theorem m13_3_0_11_9 : go 13 7 9 [3, 0, 11, 9] = true := by decide +kernel

theorem m13_3_0_11 : go 13 7 10 [3, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_11_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_11_4
  · exact m13_3_0_11_5
  · exact absurd hs (by decide)
  · exact m13_3_0_11_7
  · exact m13_3_0_11_8
  · exact m13_3_0_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_0_12_1 : go 13 7 9 [3, 0, 12, 1] = true := by decide +kernel
theorem m13_3_0_12_4 : go 13 7 9 [3, 0, 12, 4] = true := by decide +kernel
theorem m13_3_0_12_5 : go 13 7 9 [3, 0, 12, 5] = true := by decide +kernel
theorem m13_3_0_12_7 : go 13 7 9 [3, 0, 12, 7] = true := by decide +kernel
theorem m13_3_0_12_8 : go 13 7 9 [3, 0, 12, 8] = true := by decide +kernel
theorem m13_3_0_12_9 : go 13 7 9 [3, 0, 12, 9] = true := by decide +kernel
theorem m13_3_0_12_10 : go 13 7 9 [3, 0, 12, 10] = true := by decide +kernel

theorem m13_3_0_12 : go 13 7 10 [3, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_0_12_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_12_4
  · exact m13_3_0_12_5
  · exact absurd hs (by decide)
  · exact m13_3_0_12_7
  · exact m13_3_0_12_8
  · exact m13_3_0_12_9
  · exact m13_3_0_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_0 : go 13 7 11 [3, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_0_2
  · exact absurd hs (by decide)
  · exact m13_3_0_4
  · exact absurd hs (by decide)
  · exact m13_3_0_6
  · exact m13_3_0_7
  · exact m13_3_0_8
  · exact m13_3_0_9
  · exact m13_3_0_10
  · exact m13_3_0_11
  · exact m13_3_0_12

end Misses
