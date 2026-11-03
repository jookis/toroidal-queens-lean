import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [11, 7]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_11_7_0_2 : go 13 7 9 [11, 7, 0, 2] = true := by decide +kernel
theorem m13_11_7_0_3 : go 13 7 9 [11, 7, 0, 3] = true := by decide +kernel
theorem m13_11_7_0_4 : go 13 7 9 [11, 7, 0, 4] = true := by decide +kernel
theorem m13_11_7_0_6 : go 13 7 9 [11, 7, 0, 6] = true := by decide +kernel
theorem m13_11_7_0_10 : go 13 7 9 [11, 7, 0, 10] = true := by decide +kernel
theorem m13_11_7_0_12 : go 13 7 9 [11, 7, 0, 12] = true := by decide +kernel

theorem m13_11_7_0 : go 13 7 10 [11, 7, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_0_2
  · exact m13_11_7_0_3
  · exact m13_11_7_0_4
  · exact absurd hs (by decide)
  · exact m13_11_7_0_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_0_10
  · exact absurd hs (by decide)
  · exact m13_11_7_0_12

theorem m13_11_7_1_3 : go 13 7 9 [11, 7, 1, 3] = true := by decide +kernel
theorem m13_11_7_1_4 : go 13 7 9 [11, 7, 1, 4] = true := by decide +kernel
theorem m13_11_7_1_6 : go 13 7 9 [11, 7, 1, 6] = true := by decide +kernel
theorem m13_11_7_1_10 : go 13 7 9 [11, 7, 1, 10] = true := by decide +kernel
theorem m13_11_7_1_12 : go 13 7 9 [11, 7, 1, 12] = true := by decide +kernel

theorem m13_11_7_1 : go 13 7 10 [11, 7, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_1_3
  · exact m13_11_7_1_4
  · exact absurd hs (by decide)
  · exact m13_11_7_1_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_1_10
  · exact absurd hs (by decide)
  · exact m13_11_7_1_12

theorem m13_11_7_2_0 : go 13 7 9 [11, 7, 2, 0] = true := by decide +kernel
theorem m13_11_7_2_4 : go 13 7 9 [11, 7, 2, 4] = true := by decide +kernel
theorem m13_11_7_2_6 : go 13 7 9 [11, 7, 2, 6] = true := by decide +kernel
theorem m13_11_7_2_10 : go 13 7 9 [11, 7, 2, 10] = true := by decide +kernel
theorem m13_11_7_2_12 : go 13 7 9 [11, 7, 2, 12] = true := by decide +kernel

theorem m13_11_7_2 : go 13 7 10 [11, 7, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_2_4
  · exact absurd hs (by decide)
  · exact m13_11_7_2_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_2_10
  · exact absurd hs (by decide)
  · exact m13_11_7_2_12

theorem m13_11_7_3_0 : go 13 7 9 [11, 7, 3, 0] = true := by decide +kernel
theorem m13_11_7_3_1 : go 13 7 9 [11, 7, 3, 1] = true := by decide +kernel
theorem m13_11_7_3_6 : go 13 7 9 [11, 7, 3, 6] = true := by decide +kernel
theorem m13_11_7_3_10 : go 13 7 9 [11, 7, 3, 10] = true := by decide +kernel
theorem m13_11_7_3_12 : go 13 7 9 [11, 7, 3, 12] = true := by decide +kernel

theorem m13_11_7_3 : go 13 7 10 [11, 7, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_3_0
  · exact m13_11_7_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_3_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_3_10
  · exact absurd hs (by decide)
  · exact m13_11_7_3_12

theorem m13_11_7_4_0 : go 13 7 9 [11, 7, 4, 0] = true := by decide +kernel
theorem m13_11_7_4_1 : go 13 7 9 [11, 7, 4, 1] = true := by decide +kernel
theorem m13_11_7_4_2 : go 13 7 9 [11, 7, 4, 2] = true := by decide +kernel
theorem m13_11_7_4_6 : go 13 7 9 [11, 7, 4, 6] = true := by decide +kernel
theorem m13_11_7_4_10 : go 13 7 9 [11, 7, 4, 10] = true := by decide +kernel
theorem m13_11_7_4_12 : go 13 7 9 [11, 7, 4, 12] = true := by decide +kernel

theorem m13_11_7_4 : go 13 7 10 [11, 7, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_4_0
  · exact m13_11_7_4_1
  · exact m13_11_7_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_4_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_4_10
  · exact absurd hs (by decide)
  · exact m13_11_7_4_12

theorem m13_11_7_5_0 : go 13 7 9 [11, 7, 5, 0] = true := by decide +kernel
theorem m13_11_7_5_1 : go 13 7 9 [11, 7, 5, 1] = true := by decide +kernel
theorem m13_11_7_5_2 : go 13 7 9 [11, 7, 5, 2] = true := by decide +kernel
theorem m13_11_7_5_3 : go 13 7 9 [11, 7, 5, 3] = true := by decide +kernel
theorem m13_11_7_5_10 : go 13 7 9 [11, 7, 5, 10] = true := by decide +kernel
theorem m13_11_7_5_12 : go 13 7 9 [11, 7, 5, 12] = true := by decide +kernel

theorem m13_11_7_5 : go 13 7 10 [11, 7, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_5_0
  · exact m13_11_7_5_1
  · exact m13_11_7_5_2
  · exact m13_11_7_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_5_10
  · exact absurd hs (by decide)
  · exact m13_11_7_5_12

theorem m13_11_7_10_0 : go 13 7 9 [11, 7, 10, 0] = true := by decide +kernel
theorem m13_11_7_10_1 : go 13 7 9 [11, 7, 10, 1] = true := by decide +kernel
theorem m13_11_7_10_2 : go 13 7 9 [11, 7, 10, 2] = true := by decide +kernel
theorem m13_11_7_10_3 : go 13 7 9 [11, 7, 10, 3] = true := by decide +kernel
theorem m13_11_7_10_4 : go 13 7 9 [11, 7, 10, 4] = true := by decide +kernel
theorem m13_11_7_10_6 : go 13 7 9 [11, 7, 10, 6] = true := by decide +kernel
theorem m13_11_7_10_12 : go 13 7 9 [11, 7, 10, 12] = true := by decide +kernel

theorem m13_11_7_10 : go 13 7 10 [11, 7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_10_0
  · exact m13_11_7_10_1
  · exact m13_11_7_10_2
  · exact m13_11_7_10_3
  · exact m13_11_7_10_4
  · exact absurd hs (by decide)
  · exact m13_11_7_10_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_10_12

theorem m13_11_7_12_0 : go 13 7 9 [11, 7, 12, 0] = true := by decide +kernel
theorem m13_11_7_12_1 : go 13 7 9 [11, 7, 12, 1] = true := by decide +kernel
theorem m13_11_7_12_2 : go 13 7 9 [11, 7, 12, 2] = true := by decide +kernel
theorem m13_11_7_12_3 : go 13 7 9 [11, 7, 12, 3] = true := by decide +kernel
theorem m13_11_7_12_4 : go 13 7 9 [11, 7, 12, 4] = true := by decide +kernel
theorem m13_11_7_12_6 : go 13 7 9 [11, 7, 12, 6] = true := by decide +kernel
theorem m13_11_7_12_10 : go 13 7 9 [11, 7, 12, 10] = true := by decide +kernel

theorem m13_11_7_12 : go 13 7 10 [11, 7, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_12_0
  · exact m13_11_7_12_1
  · exact m13_11_7_12_2
  · exact m13_11_7_12_3
  · exact m13_11_7_12_4
  · exact absurd hs (by decide)
  · exact m13_11_7_12_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_11_7 : go 13 7 11 [11, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_7_0
  · exact m13_11_7_1
  · exact m13_11_7_2
  · exact m13_11_7_3
  · exact m13_11_7_4
  · exact m13_11_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_7_10
  · exact absurd hs (by decide)
  · exact m13_11_7_12

end Misses
