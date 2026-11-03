import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [6, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_6_0_2_4 : go 13 7 9 [6, 0, 2, 4] = true := by decide +kernel
theorem m13_6_0_2_5 : go 13 7 9 [6, 0, 2, 5] = true := by decide +kernel
theorem m13_6_0_2_7 : go 13 7 9 [6, 0, 2, 7] = true := by decide +kernel
theorem m13_6_0_2_8 : go 13 7 9 [6, 0, 2, 8] = true := by decide +kernel
theorem m13_6_0_2_10 : go 13 7 9 [6, 0, 2, 10] = true := by decide +kernel
theorem m13_6_0_2_11 : go 13 7 9 [6, 0, 2, 11] = true := by decide +kernel
theorem m13_6_0_2_12 : go 13 7 9 [6, 0, 2, 12] = true := by decide +kernel

theorem m13_6_0_2 : go 13 7 10 [6, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_2_4
  · exact m13_6_0_2_5
  · exact absurd hs (by decide)
  · exact m13_6_0_2_7
  · exact m13_6_0_2_8
  · exact absurd hs (by decide)
  · exact m13_6_0_2_10
  · exact m13_6_0_2_11
  · exact m13_6_0_2_12

theorem m13_6_0_3_1 : go 13 7 9 [6, 0, 3, 1] = true := by decide +kernel
theorem m13_6_0_3_5 : go 13 7 9 [6, 0, 3, 5] = true := by decide +kernel
theorem m13_6_0_3_7 : go 13 7 9 [6, 0, 3, 7] = true := by decide +kernel
theorem m13_6_0_3_8 : go 13 7 9 [6, 0, 3, 8] = true := by decide +kernel
theorem m13_6_0_3_10 : go 13 7 9 [6, 0, 3, 10] = true := by decide +kernel
theorem m13_6_0_3_11 : go 13 7 9 [6, 0, 3, 11] = true := by decide +kernel
theorem m13_6_0_3_12 : go 13 7 9 [6, 0, 3, 12] = true := by decide +kernel

theorem m13_6_0_3 : go 13 7 10 [6, 0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_3_5
  · exact absurd hs (by decide)
  · exact m13_6_0_3_7
  · exact m13_6_0_3_8
  · exact absurd hs (by decide)
  · exact m13_6_0_3_10
  · exact m13_6_0_3_11
  · exact m13_6_0_3_12

theorem m13_6_0_5_1 : go 13 7 9 [6, 0, 5, 1] = true := by decide +kernel
theorem m13_6_0_5_7 : go 13 7 9 [6, 0, 5, 7] = true := by decide +kernel
theorem m13_6_0_5_8 : go 13 7 9 [6, 0, 5, 8] = true := by decide +kernel
theorem m13_6_0_5_10 : go 13 7 9 [6, 0, 5, 10] = true := by decide +kernel
theorem m13_6_0_5_11 : go 13 7 9 [6, 0, 5, 11] = true := by decide +kernel
theorem m13_6_0_5_12 : go 13 7 9 [6, 0, 5, 12] = true := by decide +kernel

theorem m13_6_0_5 : go 13 7 10 [6, 0, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_5_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_5_7
  · exact m13_6_0_5_8
  · exact absurd hs (by decide)
  · exact m13_6_0_5_10
  · exact m13_6_0_5_11
  · exact m13_6_0_5_12

theorem m13_6_0_7_1 : go 13 7 9 [6, 0, 7, 1] = true := by decide +kernel
theorem m13_6_0_7_4 : go 13 7 9 [6, 0, 7, 4] = true := by decide +kernel
theorem m13_6_0_7_5 : go 13 7 9 [6, 0, 7, 5] = true := by decide +kernel
theorem m13_6_0_7_10 : go 13 7 9 [6, 0, 7, 10] = true := by decide +kernel
theorem m13_6_0_7_11 : go 13 7 9 [6, 0, 7, 11] = true := by decide +kernel
theorem m13_6_0_7_12 : go 13 7 9 [6, 0, 7, 12] = true := by decide +kernel

theorem m13_6_0_7 : go 13 7 10 [6, 0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_7_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_7_4
  · exact m13_6_0_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_7_10
  · exact m13_6_0_7_11
  · exact m13_6_0_7_12

theorem m13_6_0_9_1 : go 13 7 9 [6, 0, 9, 1] = true := by decide +kernel
theorem m13_6_0_9_4 : go 13 7 9 [6, 0, 9, 4] = true := by decide +kernel
theorem m13_6_0_9_5 : go 13 7 9 [6, 0, 9, 5] = true := by decide +kernel
theorem m13_6_0_9_7 : go 13 7 9 [6, 0, 9, 7] = true := by decide +kernel
theorem m13_6_0_9_11 : go 13 7 9 [6, 0, 9, 11] = true := by decide +kernel
theorem m13_6_0_9_12 : go 13 7 9 [6, 0, 9, 12] = true := by decide +kernel

theorem m13_6_0_9 : go 13 7 10 [6, 0, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_9_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_9_4
  · exact m13_6_0_9_5
  · exact absurd hs (by decide)
  · exact m13_6_0_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_9_11
  · exact m13_6_0_9_12

theorem m13_6_0_10_1 : go 13 7 9 [6, 0, 10, 1] = true := by decide +kernel
theorem m13_6_0_10_4 : go 13 7 9 [6, 0, 10, 4] = true := by decide +kernel
theorem m13_6_0_10_5 : go 13 7 9 [6, 0, 10, 5] = true := by decide +kernel
theorem m13_6_0_10_7 : go 13 7 9 [6, 0, 10, 7] = true := by decide +kernel
theorem m13_6_0_10_8 : go 13 7 9 [6, 0, 10, 8] = true := by decide +kernel
theorem m13_6_0_10_12 : go 13 7 9 [6, 0, 10, 12] = true := by decide +kernel

theorem m13_6_0_10 : go 13 7 10 [6, 0, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_10_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_10_4
  · exact m13_6_0_10_5
  · exact absurd hs (by decide)
  · exact m13_6_0_10_7
  · exact m13_6_0_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_10_12

theorem m13_6_0_11_1 : go 13 7 9 [6, 0, 11, 1] = true := by decide +kernel
theorem m13_6_0_11_4 : go 13 7 9 [6, 0, 11, 4] = true := by decide +kernel
theorem m13_6_0_11_5 : go 13 7 9 [6, 0, 11, 5] = true := by decide +kernel
theorem m13_6_0_11_7 : go 13 7 9 [6, 0, 11, 7] = true := by decide +kernel
theorem m13_6_0_11_8 : go 13 7 9 [6, 0, 11, 8] = true := by decide +kernel

theorem m13_6_0_11 : go 13 7 10 [6, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_11_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_11_4
  · exact m13_6_0_11_5
  · exact absurd hs (by decide)
  · exact m13_6_0_11_7
  · exact m13_6_0_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_0_12_1 : go 13 7 9 [6, 0, 12, 1] = true := by decide +kernel
theorem m13_6_0_12_4 : go 13 7 9 [6, 0, 12, 4] = true := by decide +kernel
theorem m13_6_0_12_5 : go 13 7 9 [6, 0, 12, 5] = true := by decide +kernel
theorem m13_6_0_12_7 : go 13 7 9 [6, 0, 12, 7] = true := by decide +kernel
theorem m13_6_0_12_8 : go 13 7 9 [6, 0, 12, 8] = true := by decide +kernel
theorem m13_6_0_12_10 : go 13 7 9 [6, 0, 12, 10] = true := by decide +kernel

theorem m13_6_0_12 : go 13 7 10 [6, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_6_0_12_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_12_4
  · exact m13_6_0_12_5
  · exact absurd hs (by decide)
  · exact m13_6_0_12_7
  · exact m13_6_0_12_8
  · exact absurd hs (by decide)
  · exact m13_6_0_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_0 : go 13 7 11 [6, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_0_2
  · exact m13_6_0_3
  · exact absurd hs (by decide)
  · exact m13_6_0_5
  · exact absurd hs (by decide)
  · exact m13_6_0_7
  · exact absurd hs (by decide)
  · exact m13_6_0_9
  · exact m13_6_0_10
  · exact m13_6_0_11
  · exact m13_6_0_12

end Misses
