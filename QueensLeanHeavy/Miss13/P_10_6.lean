import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [10, 6]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_10_6_0_2 : go 13 7 9 [10, 6, 0, 2] = true := by decide +kernel
theorem m13_10_6_0_3 : go 13 7 9 [10, 6, 0, 3] = true := by decide +kernel
theorem m13_10_6_0_5 : go 13 7 9 [10, 6, 0, 5] = true := by decide +kernel
theorem m13_10_6_0_9 : go 13 7 9 [10, 6, 0, 9] = true := by decide +kernel
theorem m13_10_6_0_11 : go 13 7 9 [10, 6, 0, 11] = true := by decide +kernel
theorem m13_10_6_0_12 : go 13 7 9 [10, 6, 0, 12] = true := by decide +kernel

theorem m13_10_6_0 : go 13 7 10 [10, 6, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_0_2
  · exact m13_10_6_0_3
  · exact absurd hs (by decide)
  · exact m13_10_6_0_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_0_9
  · exact absurd hs (by decide)
  · exact m13_10_6_0_11
  · exact m13_10_6_0_12

theorem m13_10_6_1_3 : go 13 7 9 [10, 6, 1, 3] = true := by decide +kernel
theorem m13_10_6_1_5 : go 13 7 9 [10, 6, 1, 5] = true := by decide +kernel
theorem m13_10_6_1_9 : go 13 7 9 [10, 6, 1, 9] = true := by decide +kernel
theorem m13_10_6_1_11 : go 13 7 9 [10, 6, 1, 11] = true := by decide +kernel
theorem m13_10_6_1_12 : go 13 7 9 [10, 6, 1, 12] = true := by decide +kernel

theorem m13_10_6_1 : go 13 7 10 [10, 6, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_1_3
  · exact absurd hs (by decide)
  · exact m13_10_6_1_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_1_9
  · exact absurd hs (by decide)
  · exact m13_10_6_1_11
  · exact m13_10_6_1_12

theorem m13_10_6_2_0 : go 13 7 9 [10, 6, 2, 0] = true := by decide +kernel
theorem m13_10_6_2_5 : go 13 7 9 [10, 6, 2, 5] = true := by decide +kernel
theorem m13_10_6_2_9 : go 13 7 9 [10, 6, 2, 9] = true := by decide +kernel
theorem m13_10_6_2_11 : go 13 7 9 [10, 6, 2, 11] = true := by decide +kernel
theorem m13_10_6_2_12 : go 13 7 9 [10, 6, 2, 12] = true := by decide +kernel

theorem m13_10_6_2 : go 13 7 10 [10, 6, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_6_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_2_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_2_9
  · exact absurd hs (by decide)
  · exact m13_10_6_2_11
  · exact m13_10_6_2_12

theorem m13_10_6_3_0 : go 13 7 9 [10, 6, 3, 0] = true := by decide +kernel
theorem m13_10_6_3_1 : go 13 7 9 [10, 6, 3, 1] = true := by decide +kernel
theorem m13_10_6_3_5 : go 13 7 9 [10, 6, 3, 5] = true := by decide +kernel
theorem m13_10_6_3_9 : go 13 7 9 [10, 6, 3, 9] = true := by decide +kernel
theorem m13_10_6_3_11 : go 13 7 9 [10, 6, 3, 11] = true := by decide +kernel
theorem m13_10_6_3_12 : go 13 7 9 [10, 6, 3, 12] = true := by decide +kernel

theorem m13_10_6_3 : go 13 7 10 [10, 6, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_6_3_0
  · exact m13_10_6_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_3_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_3_9
  · exact absurd hs (by decide)
  · exact m13_10_6_3_11
  · exact m13_10_6_3_12

theorem m13_10_6_4_0 : go 13 7 9 [10, 6, 4, 0] = true := by decide +kernel
theorem m13_10_6_4_1 : go 13 7 9 [10, 6, 4, 1] = true := by decide +kernel
theorem m13_10_6_4_2 : go 13 7 9 [10, 6, 4, 2] = true := by decide +kernel
theorem m13_10_6_4_9 : go 13 7 9 [10, 6, 4, 9] = true := by decide +kernel
theorem m13_10_6_4_11 : go 13 7 9 [10, 6, 4, 11] = true := by decide +kernel
theorem m13_10_6_4_12 : go 13 7 9 [10, 6, 4, 12] = true := by decide +kernel

theorem m13_10_6_4 : go 13 7 10 [10, 6, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_6_4_0
  · exact m13_10_6_4_1
  · exact m13_10_6_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_4_9
  · exact absurd hs (by decide)
  · exact m13_10_6_4_11
  · exact m13_10_6_4_12

theorem m13_10_6_9_0 : go 13 7 9 [10, 6, 9, 0] = true := by decide +kernel
theorem m13_10_6_9_1 : go 13 7 9 [10, 6, 9, 1] = true := by decide +kernel
theorem m13_10_6_9_2 : go 13 7 9 [10, 6, 9, 2] = true := by decide +kernel
theorem m13_10_6_9_3 : go 13 7 9 [10, 6, 9, 3] = true := by decide +kernel
theorem m13_10_6_9_5 : go 13 7 9 [10, 6, 9, 5] = true := by decide +kernel
theorem m13_10_6_9_11 : go 13 7 9 [10, 6, 9, 11] = true := by decide +kernel
theorem m13_10_6_9_12 : go 13 7 9 [10, 6, 9, 12] = true := by decide +kernel

theorem m13_10_6_9 : go 13 7 10 [10, 6, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_6_9_0
  · exact m13_10_6_9_1
  · exact m13_10_6_9_2
  · exact m13_10_6_9_3
  · exact absurd hs (by decide)
  · exact m13_10_6_9_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_9_11
  · exact m13_10_6_9_12

theorem m13_10_6_11_0 : go 13 7 9 [10, 6, 11, 0] = true := by decide +kernel
theorem m13_10_6_11_1 : go 13 7 9 [10, 6, 11, 1] = true := by decide +kernel
theorem m13_10_6_11_2 : go 13 7 9 [10, 6, 11, 2] = true := by decide +kernel
theorem m13_10_6_11_3 : go 13 7 9 [10, 6, 11, 3] = true := by decide +kernel
theorem m13_10_6_11_5 : go 13 7 9 [10, 6, 11, 5] = true := by decide +kernel
theorem m13_10_6_11_9 : go 13 7 9 [10, 6, 11, 9] = true := by decide +kernel

theorem m13_10_6_11 : go 13 7 10 [10, 6, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_6_11_0
  · exact m13_10_6_11_1
  · exact m13_10_6_11_2
  · exact m13_10_6_11_3
  · exact absurd hs (by decide)
  · exact m13_10_6_11_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_10_6 : go 13 7 11 [10, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_10_6_0
  · exact m13_10_6_1
  · exact m13_10_6_2
  · exact m13_10_6_3
  · exact m13_10_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_10_6_9
  · exact absurd hs (by decide)
  · exact m13_10_6_11
  · exact absurd hs (by decide)

end Misses
