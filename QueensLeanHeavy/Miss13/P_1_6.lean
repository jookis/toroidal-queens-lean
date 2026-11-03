import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [1, 6]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_1_6_0_2 : go 13 7 9 [1, 6, 0, 2] = true := by decide +kernel
theorem m13_1_6_0_3 : go 13 7 9 [1, 6, 0, 3] = true := by decide +kernel
theorem m13_1_6_0_5 : go 13 7 9 [1, 6, 0, 5] = true := by decide +kernel
theorem m13_1_6_0_7 : go 13 7 9 [1, 6, 0, 7] = true := by decide +kernel
theorem m13_1_6_0_9 : go 13 7 9 [1, 6, 0, 9] = true := by decide +kernel
theorem m13_1_6_0_10 : go 13 7 9 [1, 6, 0, 10] = true := by decide +kernel
theorem m13_1_6_0_11 : go 13 7 9 [1, 6, 0, 11] = true := by decide +kernel
theorem m13_1_6_0_12 : go 13 7 9 [1, 6, 0, 12] = true := by decide +kernel

theorem m13_1_6_0 : go 13 7 10 [1, 6, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_0_2
  · exact m13_1_6_0_3
  · exact absurd hs (by decide)
  · exact m13_1_6_0_5
  · exact absurd hs (by decide)
  · exact m13_1_6_0_7
  · exact absurd hs (by decide)
  · exact m13_1_6_0_9
  · exact m13_1_6_0_10
  · exact m13_1_6_0_11
  · exact m13_1_6_0_12

theorem m13_1_6_2_0 : go 13 7 9 [1, 6, 2, 0] = true := by decide +kernel
theorem m13_1_6_2_5 : go 13 7 9 [1, 6, 2, 5] = true := by decide +kernel
theorem m13_1_6_2_7 : go 13 7 9 [1, 6, 2, 7] = true := by decide +kernel
theorem m13_1_6_2_9 : go 13 7 9 [1, 6, 2, 9] = true := by decide +kernel
theorem m13_1_6_2_10 : go 13 7 9 [1, 6, 2, 10] = true := by decide +kernel
theorem m13_1_6_2_11 : go 13 7 9 [1, 6, 2, 11] = true := by decide +kernel
theorem m13_1_6_2_12 : go 13 7 9 [1, 6, 2, 12] = true := by decide +kernel

theorem m13_1_6_2 : go 13 7 10 [1, 6, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_2_5
  · exact absurd hs (by decide)
  · exact m13_1_6_2_7
  · exact absurd hs (by decide)
  · exact m13_1_6_2_9
  · exact m13_1_6_2_10
  · exact m13_1_6_2_11
  · exact m13_1_6_2_12

theorem m13_1_6_4_0 : go 13 7 9 [1, 6, 4, 0] = true := by decide +kernel
theorem m13_1_6_4_2 : go 13 7 9 [1, 6, 4, 2] = true := by decide +kernel
theorem m13_1_6_4_7 : go 13 7 9 [1, 6, 4, 7] = true := by decide +kernel
theorem m13_1_6_4_9 : go 13 7 9 [1, 6, 4, 9] = true := by decide +kernel
theorem m13_1_6_4_10 : go 13 7 9 [1, 6, 4, 10] = true := by decide +kernel
theorem m13_1_6_4_11 : go 13 7 9 [1, 6, 4, 11] = true := by decide +kernel
theorem m13_1_6_4_12 : go 13 7 9 [1, 6, 4, 12] = true := by decide +kernel

theorem m13_1_6_4 : go 13 7 10 [1, 6, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_4_0
  · exact absurd hs (by decide)
  · exact m13_1_6_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_4_7
  · exact absurd hs (by decide)
  · exact m13_1_6_4_9
  · exact m13_1_6_4_10
  · exact m13_1_6_4_11
  · exact m13_1_6_4_12

theorem m13_1_6_8_0 : go 13 7 9 [1, 6, 8, 0] = true := by decide +kernel
theorem m13_1_6_8_2 : go 13 7 9 [1, 6, 8, 2] = true := by decide +kernel
theorem m13_1_6_8_3 : go 13 7 9 [1, 6, 8, 3] = true := by decide +kernel
theorem m13_1_6_8_5 : go 13 7 9 [1, 6, 8, 5] = true := by decide +kernel
theorem m13_1_6_8_10 : go 13 7 9 [1, 6, 8, 10] = true := by decide +kernel
theorem m13_1_6_8_11 : go 13 7 9 [1, 6, 8, 11] = true := by decide +kernel
theorem m13_1_6_8_12 : go 13 7 9 [1, 6, 8, 12] = true := by decide +kernel

theorem m13_1_6_8 : go 13 7 10 [1, 6, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_8_0
  · exact absurd hs (by decide)
  · exact m13_1_6_8_2
  · exact m13_1_6_8_3
  · exact absurd hs (by decide)
  · exact m13_1_6_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_8_10
  · exact m13_1_6_8_11
  · exact m13_1_6_8_12

theorem m13_1_6_9_0 : go 13 7 9 [1, 6, 9, 0] = true := by decide +kernel
theorem m13_1_6_9_2 : go 13 7 9 [1, 6, 9, 2] = true := by decide +kernel
theorem m13_1_6_9_3 : go 13 7 9 [1, 6, 9, 3] = true := by decide +kernel
theorem m13_1_6_9_5 : go 13 7 9 [1, 6, 9, 5] = true := by decide +kernel
theorem m13_1_6_9_7 : go 13 7 9 [1, 6, 9, 7] = true := by decide +kernel
theorem m13_1_6_9_11 : go 13 7 9 [1, 6, 9, 11] = true := by decide +kernel
theorem m13_1_6_9_12 : go 13 7 9 [1, 6, 9, 12] = true := by decide +kernel

theorem m13_1_6_9 : go 13 7 10 [1, 6, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_9_0
  · exact absurd hs (by decide)
  · exact m13_1_6_9_2
  · exact m13_1_6_9_3
  · exact absurd hs (by decide)
  · exact m13_1_6_9_5
  · exact absurd hs (by decide)
  · exact m13_1_6_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_9_11
  · exact m13_1_6_9_12

theorem m13_1_6_10_0 : go 13 7 9 [1, 6, 10, 0] = true := by decide +kernel
theorem m13_1_6_10_2 : go 13 7 9 [1, 6, 10, 2] = true := by decide +kernel
theorem m13_1_6_10_3 : go 13 7 9 [1, 6, 10, 3] = true := by decide +kernel
theorem m13_1_6_10_5 : go 13 7 9 [1, 6, 10, 5] = true := by decide +kernel
theorem m13_1_6_10_7 : go 13 7 9 [1, 6, 10, 7] = true := by decide +kernel
theorem m13_1_6_10_12 : go 13 7 9 [1, 6, 10, 12] = true := by decide +kernel

theorem m13_1_6_10 : go 13 7 10 [1, 6, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_10_0
  · exact absurd hs (by decide)
  · exact m13_1_6_10_2
  · exact m13_1_6_10_3
  · exact absurd hs (by decide)
  · exact m13_1_6_10_5
  · exact absurd hs (by decide)
  · exact m13_1_6_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_10_12

theorem m13_1_6_11_0 : go 13 7 9 [1, 6, 11, 0] = true := by decide +kernel
theorem m13_1_6_11_2 : go 13 7 9 [1, 6, 11, 2] = true := by decide +kernel
theorem m13_1_6_11_3 : go 13 7 9 [1, 6, 11, 3] = true := by decide +kernel
theorem m13_1_6_11_5 : go 13 7 9 [1, 6, 11, 5] = true := by decide +kernel
theorem m13_1_6_11_7 : go 13 7 9 [1, 6, 11, 7] = true := by decide +kernel
theorem m13_1_6_11_9 : go 13 7 9 [1, 6, 11, 9] = true := by decide +kernel

theorem m13_1_6_11 : go 13 7 10 [1, 6, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_11_0
  · exact absurd hs (by decide)
  · exact m13_1_6_11_2
  · exact m13_1_6_11_3
  · exact absurd hs (by decide)
  · exact m13_1_6_11_5
  · exact absurd hs (by decide)
  · exact m13_1_6_11_7
  · exact absurd hs (by decide)
  · exact m13_1_6_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_6_12_0 : go 13 7 9 [1, 6, 12, 0] = true := by decide +kernel
theorem m13_1_6_12_2 : go 13 7 9 [1, 6, 12, 2] = true := by decide +kernel
theorem m13_1_6_12_3 : go 13 7 9 [1, 6, 12, 3] = true := by decide +kernel
theorem m13_1_6_12_5 : go 13 7 9 [1, 6, 12, 5] = true := by decide +kernel
theorem m13_1_6_12_7 : go 13 7 9 [1, 6, 12, 7] = true := by decide +kernel
theorem m13_1_6_12_9 : go 13 7 9 [1, 6, 12, 9] = true := by decide +kernel
theorem m13_1_6_12_10 : go 13 7 9 [1, 6, 12, 10] = true := by decide +kernel

theorem m13_1_6_12 : go 13 7 10 [1, 6, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_12_0
  · exact absurd hs (by decide)
  · exact m13_1_6_12_2
  · exact m13_1_6_12_3
  · exact absurd hs (by decide)
  · exact m13_1_6_12_5
  · exact absurd hs (by decide)
  · exact m13_1_6_12_7
  · exact absurd hs (by decide)
  · exact m13_1_6_12_9
  · exact m13_1_6_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_6 : go 13 7 11 [1, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_6_0
  · exact absurd hs (by decide)
  · exact m13_1_6_2
  · exact absurd hs (by decide)
  · exact m13_1_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_6_8
  · exact m13_1_6_9
  · exact m13_1_6_10
  · exact m13_1_6_11
  · exact m13_1_6_12

end Misses
