import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 4]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_4_1_3 : go 13 7 9 [2, 4, 1, 3] = true := by decide +kernel
theorem m13_2_4_1_7 : go 13 7 9 [2, 4, 1, 7] = true := by decide +kernel
theorem m13_2_4_1_8 : go 13 7 9 [2, 4, 1, 8] = true := by decide +kernel
theorem m13_2_4_1_9 : go 13 7 9 [2, 4, 1, 9] = true := by decide +kernel
theorem m13_2_4_1_10 : go 13 7 9 [2, 4, 1, 10] = true := by decide +kernel
theorem m13_2_4_1_11 : go 13 7 9 [2, 4, 1, 11] = true := by decide +kernel
theorem m13_2_4_1_12 : go 13 7 9 [2, 4, 1, 12] = true := by decide +kernel

theorem m13_2_4_1 : go 13 7 10 [2, 4, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_1_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_1_7
  · exact m13_2_4_1_8
  · exact m13_2_4_1_9
  · exact m13_2_4_1_10
  · exact m13_2_4_1_11
  · exact m13_2_4_1_12

theorem m13_2_4_6_0 : go 13 7 9 [2, 4, 6, 0] = true := by decide +kernel
theorem m13_2_4_6_1 : go 13 7 9 [2, 4, 6, 1] = true := by decide +kernel
theorem m13_2_4_6_3 : go 13 7 9 [2, 4, 6, 3] = true := by decide +kernel
theorem m13_2_4_6_8 : go 13 7 9 [2, 4, 6, 8] = true := by decide +kernel
theorem m13_2_4_6_9 : go 13 7 9 [2, 4, 6, 9] = true := by decide +kernel
theorem m13_2_4_6_10 : go 13 7 9 [2, 4, 6, 10] = true := by decide +kernel
theorem m13_2_4_6_11 : go 13 7 9 [2, 4, 6, 11] = true := by decide +kernel
theorem m13_2_4_6_12 : go 13 7 9 [2, 4, 6, 12] = true := by decide +kernel

theorem m13_2_4_6 : go 13 7 10 [2, 4, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_6_0
  · exact m13_2_4_6_1
  · exact absurd hs (by decide)
  · exact m13_2_4_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_6_8
  · exact m13_2_4_6_9
  · exact m13_2_4_6_10
  · exact m13_2_4_6_11
  · exact m13_2_4_6_12

theorem m13_2_4_7_0 : go 13 7 9 [2, 4, 7, 0] = true := by decide +kernel
theorem m13_2_4_7_1 : go 13 7 9 [2, 4, 7, 1] = true := by decide +kernel
theorem m13_2_4_7_3 : go 13 7 9 [2, 4, 7, 3] = true := by decide +kernel
theorem m13_2_4_7_9 : go 13 7 9 [2, 4, 7, 9] = true := by decide +kernel
theorem m13_2_4_7_10 : go 13 7 9 [2, 4, 7, 10] = true := by decide +kernel
theorem m13_2_4_7_11 : go 13 7 9 [2, 4, 7, 11] = true := by decide +kernel
theorem m13_2_4_7_12 : go 13 7 9 [2, 4, 7, 12] = true := by decide +kernel

theorem m13_2_4_7 : go 13 7 10 [2, 4, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_7_0
  · exact m13_2_4_7_1
  · exact absurd hs (by decide)
  · exact m13_2_4_7_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_7_9
  · exact m13_2_4_7_10
  · exact m13_2_4_7_11
  · exact m13_2_4_7_12

theorem m13_2_4_8_0 : go 13 7 9 [2, 4, 8, 0] = true := by decide +kernel
theorem m13_2_4_8_1 : go 13 7 9 [2, 4, 8, 1] = true := by decide +kernel
theorem m13_2_4_8_3 : go 13 7 9 [2, 4, 8, 3] = true := by decide +kernel
theorem m13_2_4_8_10 : go 13 7 9 [2, 4, 8, 10] = true := by decide +kernel
theorem m13_2_4_8_11 : go 13 7 9 [2, 4, 8, 11] = true := by decide +kernel
theorem m13_2_4_8_12 : go 13 7 9 [2, 4, 8, 12] = true := by decide +kernel

theorem m13_2_4_8 : go 13 7 10 [2, 4, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_8_0
  · exact m13_2_4_8_1
  · exact absurd hs (by decide)
  · exact m13_2_4_8_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_8_10
  · exact m13_2_4_8_11
  · exact m13_2_4_8_12

theorem m13_2_4_9_0 : go 13 7 9 [2, 4, 9, 0] = true := by decide +kernel
theorem m13_2_4_9_1 : go 13 7 9 [2, 4, 9, 1] = true := by decide +kernel
theorem m13_2_4_9_3 : go 13 7 9 [2, 4, 9, 3] = true := by decide +kernel
theorem m13_2_4_9_7 : go 13 7 9 [2, 4, 9, 7] = true := by decide +kernel
theorem m13_2_4_9_11 : go 13 7 9 [2, 4, 9, 11] = true := by decide +kernel
theorem m13_2_4_9_12 : go 13 7 9 [2, 4, 9, 12] = true := by decide +kernel

theorem m13_2_4_9 : go 13 7 10 [2, 4, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_9_0
  · exact m13_2_4_9_1
  · exact absurd hs (by decide)
  · exact m13_2_4_9_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_9_11
  · exact m13_2_4_9_12

theorem m13_2_4_10_0 : go 13 7 9 [2, 4, 10, 0] = true := by decide +kernel
theorem m13_2_4_10_1 : go 13 7 9 [2, 4, 10, 1] = true := by decide +kernel
theorem m13_2_4_10_3 : go 13 7 9 [2, 4, 10, 3] = true := by decide +kernel
theorem m13_2_4_10_7 : go 13 7 9 [2, 4, 10, 7] = true := by decide +kernel
theorem m13_2_4_10_8 : go 13 7 9 [2, 4, 10, 8] = true := by decide +kernel
theorem m13_2_4_10_12 : go 13 7 9 [2, 4, 10, 12] = true := by decide +kernel

theorem m13_2_4_10 : go 13 7 10 [2, 4, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_10_0
  · exact m13_2_4_10_1
  · exact absurd hs (by decide)
  · exact m13_2_4_10_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_10_7
  · exact m13_2_4_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_10_12

theorem m13_2_4_11_0 : go 13 7 9 [2, 4, 11, 0] = true := by decide +kernel
theorem m13_2_4_11_1 : go 13 7 9 [2, 4, 11, 1] = true := by decide +kernel
theorem m13_2_4_11_3 : go 13 7 9 [2, 4, 11, 3] = true := by decide +kernel
theorem m13_2_4_11_7 : go 13 7 9 [2, 4, 11, 7] = true := by decide +kernel
theorem m13_2_4_11_8 : go 13 7 9 [2, 4, 11, 8] = true := by decide +kernel
theorem m13_2_4_11_9 : go 13 7 9 [2, 4, 11, 9] = true := by decide +kernel

theorem m13_2_4_11 : go 13 7 10 [2, 4, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_11_0
  · exact m13_2_4_11_1
  · exact absurd hs (by decide)
  · exact m13_2_4_11_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_11_7
  · exact m13_2_4_11_8
  · exact m13_2_4_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_4_12_0 : go 13 7 9 [2, 4, 12, 0] = true := by decide +kernel
theorem m13_2_4_12_1 : go 13 7 9 [2, 4, 12, 1] = true := by decide +kernel
theorem m13_2_4_12_3 : go 13 7 9 [2, 4, 12, 3] = true := by decide +kernel
theorem m13_2_4_12_7 : go 13 7 9 [2, 4, 12, 7] = true := by decide +kernel
theorem m13_2_4_12_8 : go 13 7 9 [2, 4, 12, 8] = true := by decide +kernel
theorem m13_2_4_12_9 : go 13 7 9 [2, 4, 12, 9] = true := by decide +kernel
theorem m13_2_4_12_10 : go 13 7 9 [2, 4, 12, 10] = true := by decide +kernel

theorem m13_2_4_12 : go 13 7 10 [2, 4, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_4_12_0
  · exact m13_2_4_12_1
  · exact absurd hs (by decide)
  · exact m13_2_4_12_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_12_7
  · exact m13_2_4_12_8
  · exact m13_2_4_12_9
  · exact m13_2_4_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_4 : go 13 7 11 [2, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_4_6
  · exact m13_2_4_7
  · exact m13_2_4_8
  · exact m13_2_4_9
  · exact m13_2_4_10
  · exact m13_2_4_11
  · exact m13_2_4_12

end Misses
