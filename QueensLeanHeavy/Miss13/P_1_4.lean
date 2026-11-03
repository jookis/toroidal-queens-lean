import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [1, 4]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_1_4_0_3 : go 13 7 9 [1, 4, 0, 3] = true := by decide +kernel
theorem m13_1_4_0_5 : go 13 7 9 [1, 4, 0, 5] = true := by decide +kernel
theorem m13_1_4_0_7 : go 13 7 9 [1, 4, 0, 7] = true := by decide +kernel
theorem m13_1_4_0_8 : go 13 7 9 [1, 4, 0, 8] = true := by decide +kernel
theorem m13_1_4_0_9 : go 13 7 9 [1, 4, 0, 9] = true := by decide +kernel
theorem m13_1_4_0_10 : go 13 7 9 [1, 4, 0, 10] = true := by decide +kernel
theorem m13_1_4_0_11 : go 13 7 9 [1, 4, 0, 11] = true := by decide +kernel
theorem m13_1_4_0_12 : go 13 7 9 [1, 4, 0, 12] = true := by decide +kernel

theorem m13_1_4_0 : go 13 7 10 [1, 4, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_0_3
  · exact absurd hs (by decide)
  · exact m13_1_4_0_5
  · exact absurd hs (by decide)
  · exact m13_1_4_0_7
  · exact m13_1_4_0_8
  · exact m13_1_4_0_9
  · exact m13_1_4_0_10
  · exact m13_1_4_0_11
  · exact m13_1_4_0_12

theorem m13_1_4_2_0 : go 13 7 9 [1, 4, 2, 0] = true := by decide +kernel
theorem m13_1_4_2_5 : go 13 7 9 [1, 4, 2, 5] = true := by decide +kernel
theorem m13_1_4_2_7 : go 13 7 9 [1, 4, 2, 7] = true := by decide +kernel
theorem m13_1_4_2_8 : go 13 7 9 [1, 4, 2, 8] = true := by decide +kernel
theorem m13_1_4_2_9 : go 13 7 9 [1, 4, 2, 9] = true := by decide +kernel
theorem m13_1_4_2_10 : go 13 7 9 [1, 4, 2, 10] = true := by decide +kernel
theorem m13_1_4_2_11 : go 13 7 9 [1, 4, 2, 11] = true := by decide +kernel
theorem m13_1_4_2_12 : go 13 7 9 [1, 4, 2, 12] = true := by decide +kernel

theorem m13_1_4_2 : go 13 7 10 [1, 4, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_2_5
  · exact absurd hs (by decide)
  · exact m13_1_4_2_7
  · exact m13_1_4_2_8
  · exact m13_1_4_2_9
  · exact m13_1_4_2_10
  · exact m13_1_4_2_11
  · exact m13_1_4_2_12

theorem m13_1_4_6_0 : go 13 7 9 [1, 4, 6, 0] = true := by decide +kernel
theorem m13_1_4_6_3 : go 13 7 9 [1, 4, 6, 3] = true := by decide +kernel
theorem m13_1_4_6_8 : go 13 7 9 [1, 4, 6, 8] = true := by decide +kernel
theorem m13_1_4_6_9 : go 13 7 9 [1, 4, 6, 9] = true := by decide +kernel
theorem m13_1_4_6_10 : go 13 7 9 [1, 4, 6, 10] = true := by decide +kernel
theorem m13_1_4_6_11 : go 13 7 9 [1, 4, 6, 11] = true := by decide +kernel
theorem m13_1_4_6_12 : go 13 7 9 [1, 4, 6, 12] = true := by decide +kernel

theorem m13_1_4_6 : go 13 7 10 [1, 4, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_6_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_6_8
  · exact m13_1_4_6_9
  · exact m13_1_4_6_10
  · exact m13_1_4_6_11
  · exact m13_1_4_6_12

theorem m13_1_4_7_0 : go 13 7 9 [1, 4, 7, 0] = true := by decide +kernel
theorem m13_1_4_7_3 : go 13 7 9 [1, 4, 7, 3] = true := by decide +kernel
theorem m13_1_4_7_5 : go 13 7 9 [1, 4, 7, 5] = true := by decide +kernel
theorem m13_1_4_7_9 : go 13 7 9 [1, 4, 7, 9] = true := by decide +kernel
theorem m13_1_4_7_10 : go 13 7 9 [1, 4, 7, 10] = true := by decide +kernel
theorem m13_1_4_7_11 : go 13 7 9 [1, 4, 7, 11] = true := by decide +kernel
theorem m13_1_4_7_12 : go 13 7 9 [1, 4, 7, 12] = true := by decide +kernel

theorem m13_1_4_7 : go 13 7 10 [1, 4, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_7_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_7_3
  · exact absurd hs (by decide)
  · exact m13_1_4_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_7_9
  · exact m13_1_4_7_10
  · exact m13_1_4_7_11
  · exact m13_1_4_7_12

theorem m13_1_4_8_0 : go 13 7 9 [1, 4, 8, 0] = true := by decide +kernel
theorem m13_1_4_8_3 : go 13 7 9 [1, 4, 8, 3] = true := by decide +kernel
theorem m13_1_4_8_5 : go 13 7 9 [1, 4, 8, 5] = true := by decide +kernel
theorem m13_1_4_8_10 : go 13 7 9 [1, 4, 8, 10] = true := by decide +kernel
theorem m13_1_4_8_11 : go 13 7 9 [1, 4, 8, 11] = true := by decide +kernel
theorem m13_1_4_8_12 : go 13 7 9 [1, 4, 8, 12] = true := by decide +kernel

theorem m13_1_4_8 : go 13 7 10 [1, 4, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_8_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_8_3
  · exact absurd hs (by decide)
  · exact m13_1_4_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_8_10
  · exact m13_1_4_8_11
  · exact m13_1_4_8_12

theorem m13_1_4_9_0 : go 13 7 9 [1, 4, 9, 0] = true := by decide +kernel
theorem m13_1_4_9_3 : go 13 7 9 [1, 4, 9, 3] = true := by decide +kernel
theorem m13_1_4_9_5 : go 13 7 9 [1, 4, 9, 5] = true := by decide +kernel
theorem m13_1_4_9_7 : go 13 7 9 [1, 4, 9, 7] = true := by decide +kernel
theorem m13_1_4_9_11 : go 13 7 9 [1, 4, 9, 11] = true := by decide +kernel
theorem m13_1_4_9_12 : go 13 7 9 [1, 4, 9, 12] = true := by decide +kernel

theorem m13_1_4_9 : go 13 7 10 [1, 4, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_9_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_9_3
  · exact absurd hs (by decide)
  · exact m13_1_4_9_5
  · exact absurd hs (by decide)
  · exact m13_1_4_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_9_11
  · exact m13_1_4_9_12

theorem m13_1_4_10_0 : go 13 7 9 [1, 4, 10, 0] = true := by decide +kernel
theorem m13_1_4_10_3 : go 13 7 9 [1, 4, 10, 3] = true := by decide +kernel
theorem m13_1_4_10_5 : go 13 7 9 [1, 4, 10, 5] = true := by decide +kernel
theorem m13_1_4_10_7 : go 13 7 9 [1, 4, 10, 7] = true := by decide +kernel
theorem m13_1_4_10_8 : go 13 7 9 [1, 4, 10, 8] = true := by decide +kernel
theorem m13_1_4_10_12 : go 13 7 9 [1, 4, 10, 12] = true := by decide +kernel

theorem m13_1_4_10 : go 13 7 10 [1, 4, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_10_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_10_3
  · exact absurd hs (by decide)
  · exact m13_1_4_10_5
  · exact absurd hs (by decide)
  · exact m13_1_4_10_7
  · exact m13_1_4_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_10_12

theorem m13_1_4_11_0 : go 13 7 9 [1, 4, 11, 0] = true := by decide +kernel
theorem m13_1_4_11_3 : go 13 7 9 [1, 4, 11, 3] = true := by decide +kernel
theorem m13_1_4_11_5 : go 13 7 9 [1, 4, 11, 5] = true := by decide +kernel
theorem m13_1_4_11_7 : go 13 7 9 [1, 4, 11, 7] = true := by decide +kernel
theorem m13_1_4_11_8 : go 13 7 9 [1, 4, 11, 8] = true := by decide +kernel
theorem m13_1_4_11_9 : go 13 7 9 [1, 4, 11, 9] = true := by decide +kernel

theorem m13_1_4_11 : go 13 7 10 [1, 4, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_11_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_11_3
  · exact absurd hs (by decide)
  · exact m13_1_4_11_5
  · exact absurd hs (by decide)
  · exact m13_1_4_11_7
  · exact m13_1_4_11_8
  · exact m13_1_4_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_4_12_0 : go 13 7 9 [1, 4, 12, 0] = true := by decide +kernel
theorem m13_1_4_12_3 : go 13 7 9 [1, 4, 12, 3] = true := by decide +kernel
theorem m13_1_4_12_5 : go 13 7 9 [1, 4, 12, 5] = true := by decide +kernel
theorem m13_1_4_12_7 : go 13 7 9 [1, 4, 12, 7] = true := by decide +kernel
theorem m13_1_4_12_8 : go 13 7 9 [1, 4, 12, 8] = true := by decide +kernel
theorem m13_1_4_12_9 : go 13 7 9 [1, 4, 12, 9] = true := by decide +kernel
theorem m13_1_4_12_10 : go 13 7 9 [1, 4, 12, 10] = true := by decide +kernel

theorem m13_1_4_12 : go 13 7 10 [1, 4, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_12_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_12_3
  · exact absurd hs (by decide)
  · exact m13_1_4_12_5
  · exact absurd hs (by decide)
  · exact m13_1_4_12_7
  · exact m13_1_4_12_8
  · exact m13_1_4_12_9
  · exact m13_1_4_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_4 : go 13 7 11 [1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_4_0
  · exact absurd hs (by decide)
  · exact m13_1_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_4_6
  · exact m13_1_4_7
  · exact m13_1_4_8
  · exact m13_1_4_9
  · exact m13_1_4_10
  · exact m13_1_4_11
  · exact m13_1_4_12

end Misses
