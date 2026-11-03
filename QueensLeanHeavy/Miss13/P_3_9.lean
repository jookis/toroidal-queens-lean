import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 9]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_9_0_2 : go 13 7 9 [3, 9, 0, 2] = true := by decide +kernel
theorem m13_3_9_0_4 : go 13 7 9 [3, 9, 0, 4] = true := by decide +kernel
theorem m13_3_9_0_5 : go 13 7 9 [3, 9, 0, 5] = true := by decide +kernel
theorem m13_3_9_0_8 : go 13 7 9 [3, 9, 0, 8] = true := by decide +kernel
theorem m13_3_9_0_10 : go 13 7 9 [3, 9, 0, 10] = true := by decide +kernel
theorem m13_3_9_0_12 : go 13 7 9 [3, 9, 0, 12] = true := by decide +kernel

theorem m13_3_9_0 : go 13 7 10 [3, 9, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_0_2
  · exact absurd hs (by decide)
  · exact m13_3_9_0_4
  · exact m13_3_9_0_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_0_8
  · exact absurd hs (by decide)
  · exact m13_3_9_0_10
  · exact absurd hs (by decide)
  · exact m13_3_9_0_12

theorem m13_3_9_2_4 : go 13 7 9 [3, 9, 2, 4] = true := by decide +kernel
theorem m13_3_9_2_5 : go 13 7 9 [3, 9, 2, 5] = true := by decide +kernel
theorem m13_3_9_2_8 : go 13 7 9 [3, 9, 2, 8] = true := by decide +kernel
theorem m13_3_9_2_10 : go 13 7 9 [3, 9, 2, 10] = true := by decide +kernel
theorem m13_3_9_2_12 : go 13 7 9 [3, 9, 2, 12] = true := by decide +kernel

theorem m13_3_9_2 : go 13 7 10 [3, 9, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_2_4
  · exact m13_3_9_2_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_2_8
  · exact absurd hs (by decide)
  · exact m13_3_9_2_10
  · exact absurd hs (by decide)
  · exact m13_3_9_2_12

theorem m13_3_9_4_1 : go 13 7 9 [3, 9, 4, 1] = true := by decide +kernel
theorem m13_3_9_4_2 : go 13 7 9 [3, 9, 4, 2] = true := by decide +kernel
theorem m13_3_9_4_8 : go 13 7 9 [3, 9, 4, 8] = true := by decide +kernel
theorem m13_3_9_4_10 : go 13 7 9 [3, 9, 4, 10] = true := by decide +kernel
theorem m13_3_9_4_12 : go 13 7 9 [3, 9, 4, 12] = true := by decide +kernel

theorem m13_3_9_4 : go 13 7 10 [3, 9, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_9_4_1
  · exact m13_3_9_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_4_8
  · exact absurd hs (by decide)
  · exact m13_3_9_4_10
  · exact absurd hs (by decide)
  · exact m13_3_9_4_12

theorem m13_3_9_6_1 : go 13 7 9 [3, 9, 6, 1] = true := by decide +kernel
theorem m13_3_9_6_2 : go 13 7 9 [3, 9, 6, 2] = true := by decide +kernel
theorem m13_3_9_6_4 : go 13 7 9 [3, 9, 6, 4] = true := by decide +kernel
theorem m13_3_9_6_8 : go 13 7 9 [3, 9, 6, 8] = true := by decide +kernel
theorem m13_3_9_6_10 : go 13 7 9 [3, 9, 6, 10] = true := by decide +kernel
theorem m13_3_9_6_12 : go 13 7 9 [3, 9, 6, 12] = true := by decide +kernel

theorem m13_3_9_6 : go 13 7 10 [3, 9, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_9_6_1
  · exact m13_3_9_6_2
  · exact absurd hs (by decide)
  · exact m13_3_9_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_6_8
  · exact absurd hs (by decide)
  · exact m13_3_9_6_10
  · exact absurd hs (by decide)
  · exact m13_3_9_6_12

theorem m13_3_9_7_1 : go 13 7 9 [3, 9, 7, 1] = true := by decide +kernel
theorem m13_3_9_7_2 : go 13 7 9 [3, 9, 7, 2] = true := by decide +kernel
theorem m13_3_9_7_4 : go 13 7 9 [3, 9, 7, 4] = true := by decide +kernel
theorem m13_3_9_7_5 : go 13 7 9 [3, 9, 7, 5] = true := by decide +kernel
theorem m13_3_9_7_10 : go 13 7 9 [3, 9, 7, 10] = true := by decide +kernel
theorem m13_3_9_7_12 : go 13 7 9 [3, 9, 7, 12] = true := by decide +kernel

theorem m13_3_9_7 : go 13 7 10 [3, 9, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_9_7_1
  · exact m13_3_9_7_2
  · exact absurd hs (by decide)
  · exact m13_3_9_7_4
  · exact m13_3_9_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_7_10
  · exact absurd hs (by decide)
  · exact m13_3_9_7_12

theorem m13_3_9_11_1 : go 13 7 9 [3, 9, 11, 1] = true := by decide +kernel
theorem m13_3_9_11_2 : go 13 7 9 [3, 9, 11, 2] = true := by decide +kernel
theorem m13_3_9_11_4 : go 13 7 9 [3, 9, 11, 4] = true := by decide +kernel
theorem m13_3_9_11_5 : go 13 7 9 [3, 9, 11, 5] = true := by decide +kernel
theorem m13_3_9_11_8 : go 13 7 9 [3, 9, 11, 8] = true := by decide +kernel

theorem m13_3_9_11 : go 13 7 10 [3, 9, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_9_11_1
  · exact m13_3_9_11_2
  · exact absurd hs (by decide)
  · exact m13_3_9_11_4
  · exact m13_3_9_11_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_9_12_1 : go 13 7 9 [3, 9, 12, 1] = true := by decide +kernel
theorem m13_3_9_12_2 : go 13 7 9 [3, 9, 12, 2] = true := by decide +kernel
theorem m13_3_9_12_4 : go 13 7 9 [3, 9, 12, 4] = true := by decide +kernel
theorem m13_3_9_12_5 : go 13 7 9 [3, 9, 12, 5] = true := by decide +kernel
theorem m13_3_9_12_8 : go 13 7 9 [3, 9, 12, 8] = true := by decide +kernel
theorem m13_3_9_12_10 : go 13 7 9 [3, 9, 12, 10] = true := by decide +kernel

theorem m13_3_9_12 : go 13 7 10 [3, 9, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_9_12_1
  · exact m13_3_9_12_2
  · exact absurd hs (by decide)
  · exact m13_3_9_12_4
  · exact m13_3_9_12_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_12_8
  · exact absurd hs (by decide)
  · exact m13_3_9_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_9 : go 13 7 11 [3, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_3_9_0
  · exact absurd hs (by decide)
  · exact m13_3_9_2
  · exact absurd hs (by decide)
  · exact m13_3_9_4
  · exact absurd hs (by decide)
  · exact m13_3_9_6
  · exact m13_3_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_9_11
  · exact m13_3_9_12

end Misses
