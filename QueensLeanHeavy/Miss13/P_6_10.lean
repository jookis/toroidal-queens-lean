import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [6, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_6_10_0_2 : go 13 7 9 [6, 10, 0, 2] = true := by decide +kernel
theorem m13_6_10_0_4 : go 13 7 9 [6, 10, 0, 4] = true := by decide +kernel
theorem m13_6_10_0_5 : go 13 7 9 [6, 10, 0, 5] = true := by decide +kernel
theorem m13_6_10_0_7 : go 13 7 9 [6, 10, 0, 7] = true := by decide +kernel
theorem m13_6_10_0_11 : go 13 7 9 [6, 10, 0, 11] = true := by decide +kernel

theorem m13_6_10_0 : go 13 7 10 [6, 10, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_0_2
  · exact absurd hs (by decide)
  · exact m13_6_10_0_4
  · exact m13_6_10_0_5
  · exact absurd hs (by decide)
  · exact m13_6_10_0_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_0_11
  · exact absurd hs (by decide)

theorem m13_6_10_1_4 : go 13 7 9 [6, 10, 1, 4] = true := by decide +kernel
theorem m13_6_10_1_5 : go 13 7 9 [6, 10, 1, 5] = true := by decide +kernel
theorem m13_6_10_1_7 : go 13 7 9 [6, 10, 1, 7] = true := by decide +kernel
theorem m13_6_10_1_11 : go 13 7 9 [6, 10, 1, 11] = true := by decide +kernel

theorem m13_6_10_1 : go 13 7 10 [6, 10, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_1_4
  · exact m13_6_10_1_5
  · exact absurd hs (by decide)
  · exact m13_6_10_1_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_1_11
  · exact absurd hs (by decide)

theorem m13_6_10_2_0 : go 13 7 9 [6, 10, 2, 0] = true := by decide +kernel
theorem m13_6_10_2_4 : go 13 7 9 [6, 10, 2, 4] = true := by decide +kernel
theorem m13_6_10_2_5 : go 13 7 9 [6, 10, 2, 5] = true := by decide +kernel
theorem m13_6_10_2_7 : go 13 7 9 [6, 10, 2, 7] = true := by decide +kernel
theorem m13_6_10_2_11 : go 13 7 9 [6, 10, 2, 11] = true := by decide +kernel

theorem m13_6_10_2 : go 13 7 10 [6, 10, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_10_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_2_4
  · exact m13_6_10_2_5
  · exact absurd hs (by decide)
  · exact m13_6_10_2_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_2_11
  · exact absurd hs (by decide)

theorem m13_6_10_3_0 : go 13 7 9 [6, 10, 3, 0] = true := by decide +kernel
theorem m13_6_10_3_1 : go 13 7 9 [6, 10, 3, 1] = true := by decide +kernel
theorem m13_6_10_3_5 : go 13 7 9 [6, 10, 3, 5] = true := by decide +kernel
theorem m13_6_10_3_7 : go 13 7 9 [6, 10, 3, 7] = true := by decide +kernel
theorem m13_6_10_3_11 : go 13 7 9 [6, 10, 3, 11] = true := by decide +kernel

theorem m13_6_10_3 : go 13 7 10 [6, 10, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_10_3_0
  · exact m13_6_10_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_3_5
  · exact absurd hs (by decide)
  · exact m13_6_10_3_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_3_11
  · exact absurd hs (by decide)

theorem m13_6_10_5_0 : go 13 7 9 [6, 10, 5, 0] = true := by decide +kernel
theorem m13_6_10_5_1 : go 13 7 9 [6, 10, 5, 1] = true := by decide +kernel
theorem m13_6_10_5_2 : go 13 7 9 [6, 10, 5, 2] = true := by decide +kernel
theorem m13_6_10_5_7 : go 13 7 9 [6, 10, 5, 7] = true := by decide +kernel
theorem m13_6_10_5_11 : go 13 7 9 [6, 10, 5, 11] = true := by decide +kernel

theorem m13_6_10_5 : go 13 7 10 [6, 10, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_10_5_0
  · exact m13_6_10_5_1
  · exact m13_6_10_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_5_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_5_11
  · exact absurd hs (by decide)

theorem m13_6_10_7_0 : go 13 7 9 [6, 10, 7, 0] = true := by decide +kernel
theorem m13_6_10_7_1 : go 13 7 9 [6, 10, 7, 1] = true := by decide +kernel
theorem m13_6_10_7_2 : go 13 7 9 [6, 10, 7, 2] = true := by decide +kernel
theorem m13_6_10_7_4 : go 13 7 9 [6, 10, 7, 4] = true := by decide +kernel
theorem m13_6_10_7_5 : go 13 7 9 [6, 10, 7, 5] = true := by decide +kernel
theorem m13_6_10_7_11 : go 13 7 9 [6, 10, 7, 11] = true := by decide +kernel

theorem m13_6_10_7 : go 13 7 10 [6, 10, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_10_7_0
  · exact m13_6_10_7_1
  · exact m13_6_10_7_2
  · exact absurd hs (by decide)
  · exact m13_6_10_7_4
  · exact m13_6_10_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_7_11
  · exact absurd hs (by decide)

theorem m13_6_10_12_0 : go 13 7 9 [6, 10, 12, 0] = true := by decide +kernel
theorem m13_6_10_12_1 : go 13 7 9 [6, 10, 12, 1] = true := by decide +kernel
theorem m13_6_10_12_2 : go 13 7 9 [6, 10, 12, 2] = true := by decide +kernel
theorem m13_6_10_12_4 : go 13 7 9 [6, 10, 12, 4] = true := by decide +kernel
theorem m13_6_10_12_5 : go 13 7 9 [6, 10, 12, 5] = true := by decide +kernel
theorem m13_6_10_12_7 : go 13 7 9 [6, 10, 12, 7] = true := by decide +kernel

theorem m13_6_10_12 : go 13 7 10 [6, 10, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_10_12_0
  · exact m13_6_10_12_1
  · exact m13_6_10_12_2
  · exact absurd hs (by decide)
  · exact m13_6_10_12_4
  · exact m13_6_10_12_5
  · exact absurd hs (by decide)
  · exact m13_6_10_12_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_6_10 : go 13 7 11 [6, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_6_10_0
  · exact m13_6_10_1
  · exact m13_6_10_2
  · exact m13_6_10_3
  · exact absurd hs (by decide)
  · exact m13_6_10_5
  · exact absurd hs (by decide)
  · exact m13_6_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_6_10_12

end Misses
