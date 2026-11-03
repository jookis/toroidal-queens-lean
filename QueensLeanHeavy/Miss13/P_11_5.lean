import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [11, 5]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_11_5_0_2 : go 13 7 9 [11, 5, 0, 2] = true := by decide +kernel
theorem m13_11_5_0_4 : go 13 7 9 [11, 5, 0, 4] = true := by decide +kernel
theorem m13_11_5_0_6 : go 13 7 9 [11, 5, 0, 6] = true := by decide +kernel
theorem m13_11_5_0_9 : go 13 7 9 [11, 5, 0, 9] = true := by decide +kernel
theorem m13_11_5_0_10 : go 13 7 9 [11, 5, 0, 10] = true := by decide +kernel
theorem m13_11_5_0_12 : go 13 7 9 [11, 5, 0, 12] = true := by decide +kernel

theorem m13_11_5_0 : go 13 7 10 [11, 5, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_0_2
  · exact absurd hs (by decide)
  · exact m13_11_5_0_4
  · exact absurd hs (by decide)
  · exact m13_11_5_0_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_0_9
  · exact m13_11_5_0_10
  · exact absurd hs (by decide)
  · exact m13_11_5_0_12

theorem m13_11_5_1_4 : go 13 7 9 [11, 5, 1, 4] = true := by decide +kernel
theorem m13_11_5_1_6 : go 13 7 9 [11, 5, 1, 6] = true := by decide +kernel
theorem m13_11_5_1_9 : go 13 7 9 [11, 5, 1, 9] = true := by decide +kernel
theorem m13_11_5_1_10 : go 13 7 9 [11, 5, 1, 10] = true := by decide +kernel
theorem m13_11_5_1_12 : go 13 7 9 [11, 5, 1, 12] = true := by decide +kernel

theorem m13_11_5_1 : go 13 7 10 [11, 5, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_1_4
  · exact absurd hs (by decide)
  · exact m13_11_5_1_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_1_9
  · exact m13_11_5_1_10
  · exact absurd hs (by decide)
  · exact m13_11_5_1_12

theorem m13_11_5_2_0 : go 13 7 9 [11, 5, 2, 0] = true := by decide +kernel
theorem m13_11_5_2_4 : go 13 7 9 [11, 5, 2, 4] = true := by decide +kernel
theorem m13_11_5_2_6 : go 13 7 9 [11, 5, 2, 6] = true := by decide +kernel
theorem m13_11_5_2_9 : go 13 7 9 [11, 5, 2, 9] = true := by decide +kernel
theorem m13_11_5_2_10 : go 13 7 9 [11, 5, 2, 10] = true := by decide +kernel
theorem m13_11_5_2_12 : go 13 7 9 [11, 5, 2, 12] = true := by decide +kernel

theorem m13_11_5_2 : go 13 7 10 [11, 5, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_2_4
  · exact absurd hs (by decide)
  · exact m13_11_5_2_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_2_9
  · exact m13_11_5_2_10
  · exact absurd hs (by decide)
  · exact m13_11_5_2_12

theorem m13_11_5_3_0 : go 13 7 9 [11, 5, 3, 0] = true := by decide +kernel
theorem m13_11_5_3_1 : go 13 7 9 [11, 5, 3, 1] = true := by decide +kernel
theorem m13_11_5_3_6 : go 13 7 9 [11, 5, 3, 6] = true := by decide +kernel
theorem m13_11_5_3_9 : go 13 7 9 [11, 5, 3, 9] = true := by decide +kernel
theorem m13_11_5_3_10 : go 13 7 9 [11, 5, 3, 10] = true := by decide +kernel
theorem m13_11_5_3_12 : go 13 7 9 [11, 5, 3, 12] = true := by decide +kernel

theorem m13_11_5_3 : go 13 7 10 [11, 5, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_3_0
  · exact m13_11_5_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_3_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_3_9
  · exact m13_11_5_3_10
  · exact absurd hs (by decide)
  · exact m13_11_5_3_12

theorem m13_11_5_7_0 : go 13 7 9 [11, 5, 7, 0] = true := by decide +kernel
theorem m13_11_5_7_1 : go 13 7 9 [11, 5, 7, 1] = true := by decide +kernel
theorem m13_11_5_7_2 : go 13 7 9 [11, 5, 7, 2] = true := by decide +kernel
theorem m13_11_5_7_4 : go 13 7 9 [11, 5, 7, 4] = true := by decide +kernel
theorem m13_11_5_7_9 : go 13 7 9 [11, 5, 7, 9] = true := by decide +kernel
theorem m13_11_5_7_10 : go 13 7 9 [11, 5, 7, 10] = true := by decide +kernel
theorem m13_11_5_7_12 : go 13 7 9 [11, 5, 7, 12] = true := by decide +kernel

theorem m13_11_5_7 : go 13 7 10 [11, 5, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_7_0
  · exact m13_11_5_7_1
  · exact m13_11_5_7_2
  · exact absurd hs (by decide)
  · exact m13_11_5_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_7_9
  · exact m13_11_5_7_10
  · exact absurd hs (by decide)
  · exact m13_11_5_7_12

theorem m13_11_5_8_0 : go 13 7 9 [11, 5, 8, 0] = true := by decide +kernel
theorem m13_11_5_8_1 : go 13 7 9 [11, 5, 8, 1] = true := by decide +kernel
theorem m13_11_5_8_2 : go 13 7 9 [11, 5, 8, 2] = true := by decide +kernel
theorem m13_11_5_8_4 : go 13 7 9 [11, 5, 8, 4] = true := by decide +kernel
theorem m13_11_5_8_6 : go 13 7 9 [11, 5, 8, 6] = true := by decide +kernel
theorem m13_11_5_8_10 : go 13 7 9 [11, 5, 8, 10] = true := by decide +kernel
theorem m13_11_5_8_12 : go 13 7 9 [11, 5, 8, 12] = true := by decide +kernel

theorem m13_11_5_8 : go 13 7 10 [11, 5, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_8_0
  · exact m13_11_5_8_1
  · exact m13_11_5_8_2
  · exact absurd hs (by decide)
  · exact m13_11_5_8_4
  · exact absurd hs (by decide)
  · exact m13_11_5_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_8_10
  · exact absurd hs (by decide)
  · exact m13_11_5_8_12

theorem m13_11_5_10_0 : go 13 7 9 [11, 5, 10, 0] = true := by decide +kernel
theorem m13_11_5_10_1 : go 13 7 9 [11, 5, 10, 1] = true := by decide +kernel
theorem m13_11_5_10_2 : go 13 7 9 [11, 5, 10, 2] = true := by decide +kernel
theorem m13_11_5_10_4 : go 13 7 9 [11, 5, 10, 4] = true := by decide +kernel
theorem m13_11_5_10_6 : go 13 7 9 [11, 5, 10, 6] = true := by decide +kernel
theorem m13_11_5_10_12 : go 13 7 9 [11, 5, 10, 12] = true := by decide +kernel

theorem m13_11_5_10 : go 13 7 10 [11, 5, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_10_0
  · exact m13_11_5_10_1
  · exact m13_11_5_10_2
  · exact absurd hs (by decide)
  · exact m13_11_5_10_4
  · exact absurd hs (by decide)
  · exact m13_11_5_10_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_10_12

theorem m13_11_5_12_0 : go 13 7 9 [11, 5, 12, 0] = true := by decide +kernel
theorem m13_11_5_12_1 : go 13 7 9 [11, 5, 12, 1] = true := by decide +kernel
theorem m13_11_5_12_2 : go 13 7 9 [11, 5, 12, 2] = true := by decide +kernel
theorem m13_11_5_12_4 : go 13 7 9 [11, 5, 12, 4] = true := by decide +kernel
theorem m13_11_5_12_6 : go 13 7 9 [11, 5, 12, 6] = true := by decide +kernel
theorem m13_11_5_12_9 : go 13 7 9 [11, 5, 12, 9] = true := by decide +kernel
theorem m13_11_5_12_10 : go 13 7 9 [11, 5, 12, 10] = true := by decide +kernel

theorem m13_11_5_12 : go 13 7 10 [11, 5, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_12_0
  · exact m13_11_5_12_1
  · exact m13_11_5_12_2
  · exact absurd hs (by decide)
  · exact m13_11_5_12_4
  · exact absurd hs (by decide)
  · exact m13_11_5_12_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_12_9
  · exact m13_11_5_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_11_5 : go 13 7 11 [11, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_5_0
  · exact m13_11_5_1
  · exact m13_11_5_2
  · exact m13_11_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_5_7
  · exact m13_11_5_8
  · exact absurd hs (by decide)
  · exact m13_11_5_10
  · exact absurd hs (by decide)
  · exact m13_11_5_12

end Misses
