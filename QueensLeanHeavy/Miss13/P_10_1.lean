import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [10, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_10_1_3_0 : go 13 7 9 [10, 1, 3, 0] = true := by decide +kernel
theorem m13_10_1_3_5 : go 13 7 9 [10, 1, 3, 5] = true := by decide +kernel
theorem m13_10_1_3_6 : go 13 7 9 [10, 1, 3, 6] = true := by decide +kernel
theorem m13_10_1_3_8 : go 13 7 9 [10, 1, 3, 8] = true := by decide +kernel
theorem m13_10_1_3_9 : go 13 7 9 [10, 1, 3, 9] = true := by decide +kernel
theorem m13_10_1_3_11 : go 13 7 9 [10, 1, 3, 11] = true := by decide +kernel
theorem m13_10_1_3_12 : go 13 7 9 [10, 1, 3, 12] = true := by decide +kernel

theorem m13_10_1_3 : go 13 7 10 [10, 1, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_3_5
  · exact m13_10_1_3_6
  · exact absurd hs (by decide)
  · exact m13_10_1_3_8
  · exact m13_10_1_3_9
  · exact absurd hs (by decide)
  · exact m13_10_1_3_11
  · exact m13_10_1_3_12

theorem m13_10_1_4_0 : go 13 7 9 [10, 1, 4, 0] = true := by decide +kernel
theorem m13_10_1_4_2 : go 13 7 9 [10, 1, 4, 2] = true := by decide +kernel
theorem m13_10_1_4_6 : go 13 7 9 [10, 1, 4, 6] = true := by decide +kernel
theorem m13_10_1_4_8 : go 13 7 9 [10, 1, 4, 8] = true := by decide +kernel
theorem m13_10_1_4_9 : go 13 7 9 [10, 1, 4, 9] = true := by decide +kernel
theorem m13_10_1_4_11 : go 13 7 9 [10, 1, 4, 11] = true := by decide +kernel
theorem m13_10_1_4_12 : go 13 7 9 [10, 1, 4, 12] = true := by decide +kernel

theorem m13_10_1_4 : go 13 7 10 [10, 1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_4_0
  · exact absurd hs (by decide)
  · exact m13_10_1_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_4_6
  · exact absurd hs (by decide)
  · exact m13_10_1_4_8
  · exact m13_10_1_4_9
  · exact absurd hs (by decide)
  · exact m13_10_1_4_11
  · exact m13_10_1_4_12

theorem m13_10_1_5_0 : go 13 7 9 [10, 1, 5, 0] = true := by decide +kernel
theorem m13_10_1_5_2 : go 13 7 9 [10, 1, 5, 2] = true := by decide +kernel
theorem m13_10_1_5_8 : go 13 7 9 [10, 1, 5, 8] = true := by decide +kernel
theorem m13_10_1_5_9 : go 13 7 9 [10, 1, 5, 9] = true := by decide +kernel
theorem m13_10_1_5_11 : go 13 7 9 [10, 1, 5, 11] = true := by decide +kernel
theorem m13_10_1_5_12 : go 13 7 9 [10, 1, 5, 12] = true := by decide +kernel

theorem m13_10_1_5 : go 13 7 10 [10, 1, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_5_0
  · exact absurd hs (by decide)
  · exact m13_10_1_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_5_8
  · exact m13_10_1_5_9
  · exact absurd hs (by decide)
  · exact m13_10_1_5_11
  · exact m13_10_1_5_12

theorem m13_10_1_6_0 : go 13 7 9 [10, 1, 6, 0] = true := by decide +kernel
theorem m13_10_1_6_2 : go 13 7 9 [10, 1, 6, 2] = true := by decide +kernel
theorem m13_10_1_6_4 : go 13 7 9 [10, 1, 6, 4] = true := by decide +kernel
theorem m13_10_1_6_8 : go 13 7 9 [10, 1, 6, 8] = true := by decide +kernel
theorem m13_10_1_6_9 : go 13 7 9 [10, 1, 6, 9] = true := by decide +kernel
theorem m13_10_1_6_11 : go 13 7 9 [10, 1, 6, 11] = true := by decide +kernel
theorem m13_10_1_6_12 : go 13 7 9 [10, 1, 6, 12] = true := by decide +kernel

theorem m13_10_1_6 : go 13 7 10 [10, 1, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_6_0
  · exact absurd hs (by decide)
  · exact m13_10_1_6_2
  · exact absurd hs (by decide)
  · exact m13_10_1_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_6_8
  · exact m13_10_1_6_9
  · exact absurd hs (by decide)
  · exact m13_10_1_6_11
  · exact m13_10_1_6_12

theorem m13_10_1_7_0 : go 13 7 9 [10, 1, 7, 0] = true := by decide +kernel
theorem m13_10_1_7_2 : go 13 7 9 [10, 1, 7, 2] = true := by decide +kernel
theorem m13_10_1_7_4 : go 13 7 9 [10, 1, 7, 4] = true := by decide +kernel
theorem m13_10_1_7_5 : go 13 7 9 [10, 1, 7, 5] = true := by decide +kernel
theorem m13_10_1_7_9 : go 13 7 9 [10, 1, 7, 9] = true := by decide +kernel
theorem m13_10_1_7_11 : go 13 7 9 [10, 1, 7, 11] = true := by decide +kernel
theorem m13_10_1_7_12 : go 13 7 9 [10, 1, 7, 12] = true := by decide +kernel

theorem m13_10_1_7 : go 13 7 10 [10, 1, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_7_0
  · exact absurd hs (by decide)
  · exact m13_10_1_7_2
  · exact absurd hs (by decide)
  · exact m13_10_1_7_4
  · exact m13_10_1_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_7_9
  · exact absurd hs (by decide)
  · exact m13_10_1_7_11
  · exact m13_10_1_7_12

theorem m13_10_1_9_0 : go 13 7 9 [10, 1, 9, 0] = true := by decide +kernel
theorem m13_10_1_9_2 : go 13 7 9 [10, 1, 9, 2] = true := by decide +kernel
theorem m13_10_1_9_4 : go 13 7 9 [10, 1, 9, 4] = true := by decide +kernel
theorem m13_10_1_9_5 : go 13 7 9 [10, 1, 9, 5] = true := by decide +kernel
theorem m13_10_1_9_6 : go 13 7 9 [10, 1, 9, 6] = true := by decide +kernel
theorem m13_10_1_9_11 : go 13 7 9 [10, 1, 9, 11] = true := by decide +kernel
theorem m13_10_1_9_12 : go 13 7 9 [10, 1, 9, 12] = true := by decide +kernel

theorem m13_10_1_9 : go 13 7 10 [10, 1, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_9_0
  · exact absurd hs (by decide)
  · exact m13_10_1_9_2
  · exact absurd hs (by decide)
  · exact m13_10_1_9_4
  · exact m13_10_1_9_5
  · exact m13_10_1_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_9_11
  · exact m13_10_1_9_12

theorem m13_10_1_11_0 : go 13 7 9 [10, 1, 11, 0] = true := by decide +kernel
theorem m13_10_1_11_2 : go 13 7 9 [10, 1, 11, 2] = true := by decide +kernel
theorem m13_10_1_11_4 : go 13 7 9 [10, 1, 11, 4] = true := by decide +kernel
theorem m13_10_1_11_5 : go 13 7 9 [10, 1, 11, 5] = true := by decide +kernel
theorem m13_10_1_11_6 : go 13 7 9 [10, 1, 11, 6] = true := by decide +kernel
theorem m13_10_1_11_8 : go 13 7 9 [10, 1, 11, 8] = true := by decide +kernel
theorem m13_10_1_11_9 : go 13 7 9 [10, 1, 11, 9] = true := by decide +kernel

theorem m13_10_1_11 : go 13 7 10 [10, 1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_1_11_0
  · exact absurd hs (by decide)
  · exact m13_10_1_11_2
  · exact absurd hs (by decide)
  · exact m13_10_1_11_4
  · exact m13_10_1_11_5
  · exact m13_10_1_11_6
  · exact absurd hs (by decide)
  · exact m13_10_1_11_8
  · exact m13_10_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_10_1 : go 13 7 11 [10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_1_3
  · exact m13_10_1_4
  · exact m13_10_1_5
  · exact m13_10_1_6
  · exact m13_10_1_7
  · exact absurd hs (by decide)
  · exact m13_10_1_9
  · exact absurd hs (by decide)
  · exact m13_10_1_11
  · exact absurd hs (by decide)

end Misses
