import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [11, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_11_0_2_4 : go 13 7 9 [11, 0, 2, 4] = true := by decide +kernel
theorem m13_11_0_2_5 : go 13 7 9 [11, 0, 2, 5] = true := by decide +kernel
theorem m13_11_0_2_6 : go 13 7 9 [11, 0, 2, 6] = true := by decide +kernel
theorem m13_11_0_2_7 : go 13 7 9 [11, 0, 2, 7] = true := by decide +kernel
theorem m13_11_0_2_9 : go 13 7 9 [11, 0, 2, 9] = true := by decide +kernel
theorem m13_11_0_2_10 : go 13 7 9 [11, 0, 2, 10] = true := by decide +kernel
theorem m13_11_0_2_12 : go 13 7 9 [11, 0, 2, 12] = true := by decide +kernel

theorem m13_11_0_2 : go 13 7 10 [11, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_2_4
  · exact m13_11_0_2_5
  · exact m13_11_0_2_6
  · exact m13_11_0_2_7
  · exact absurd hs (by decide)
  · exact m13_11_0_2_9
  · exact m13_11_0_2_10
  · exact absurd hs (by decide)
  · exact m13_11_0_2_12

theorem m13_11_0_3_1 : go 13 7 9 [11, 0, 3, 1] = true := by decide +kernel
theorem m13_11_0_3_5 : go 13 7 9 [11, 0, 3, 5] = true := by decide +kernel
theorem m13_11_0_3_6 : go 13 7 9 [11, 0, 3, 6] = true := by decide +kernel
theorem m13_11_0_3_7 : go 13 7 9 [11, 0, 3, 7] = true := by decide +kernel
theorem m13_11_0_3_9 : go 13 7 9 [11, 0, 3, 9] = true := by decide +kernel
theorem m13_11_0_3_10 : go 13 7 9 [11, 0, 3, 10] = true := by decide +kernel
theorem m13_11_0_3_12 : go 13 7 9 [11, 0, 3, 12] = true := by decide +kernel

theorem m13_11_0_3 : go 13 7 10 [11, 0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_3_5
  · exact m13_11_0_3_6
  · exact m13_11_0_3_7
  · exact absurd hs (by decide)
  · exact m13_11_0_3_9
  · exact m13_11_0_3_10
  · exact absurd hs (by decide)
  · exact m13_11_0_3_12

theorem m13_11_0_4_1 : go 13 7 9 [11, 0, 4, 1] = true := by decide +kernel
theorem m13_11_0_4_6 : go 13 7 9 [11, 0, 4, 6] = true := by decide +kernel
theorem m13_11_0_4_7 : go 13 7 9 [11, 0, 4, 7] = true := by decide +kernel
theorem m13_11_0_4_9 : go 13 7 9 [11, 0, 4, 9] = true := by decide +kernel
theorem m13_11_0_4_10 : go 13 7 9 [11, 0, 4, 10] = true := by decide +kernel
theorem m13_11_0_4_12 : go 13 7 9 [11, 0, 4, 12] = true := by decide +kernel

theorem m13_11_0_4 : go 13 7 10 [11, 0, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_4_6
  · exact m13_11_0_4_7
  · exact absurd hs (by decide)
  · exact m13_11_0_4_9
  · exact m13_11_0_4_10
  · exact absurd hs (by decide)
  · exact m13_11_0_4_12

theorem m13_11_0_5_1 : go 13 7 9 [11, 0, 5, 1] = true := by decide +kernel
theorem m13_11_0_5_3 : go 13 7 9 [11, 0, 5, 3] = true := by decide +kernel
theorem m13_11_0_5_7 : go 13 7 9 [11, 0, 5, 7] = true := by decide +kernel
theorem m13_11_0_5_9 : go 13 7 9 [11, 0, 5, 9] = true := by decide +kernel
theorem m13_11_0_5_10 : go 13 7 9 [11, 0, 5, 10] = true := by decide +kernel
theorem m13_11_0_5_12 : go 13 7 9 [11, 0, 5, 12] = true := by decide +kernel

theorem m13_11_0_5 : go 13 7 10 [11, 0, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_5_1
  · exact absurd hs (by decide)
  · exact m13_11_0_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_5_7
  · exact absurd hs (by decide)
  · exact m13_11_0_5_9
  · exact m13_11_0_5_10
  · exact absurd hs (by decide)
  · exact m13_11_0_5_12

theorem m13_11_0_6_1 : go 13 7 9 [11, 0, 6, 1] = true := by decide +kernel
theorem m13_11_0_6_3 : go 13 7 9 [11, 0, 6, 3] = true := by decide +kernel
theorem m13_11_0_6_4 : go 13 7 9 [11, 0, 6, 4] = true := by decide +kernel
theorem m13_11_0_6_9 : go 13 7 9 [11, 0, 6, 9] = true := by decide +kernel
theorem m13_11_0_6_10 : go 13 7 9 [11, 0, 6, 10] = true := by decide +kernel
theorem m13_11_0_6_12 : go 13 7 9 [11, 0, 6, 12] = true := by decide +kernel

theorem m13_11_0_6 : go 13 7 10 [11, 0, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_6_1
  · exact absurd hs (by decide)
  · exact m13_11_0_6_3
  · exact m13_11_0_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_6_9
  · exact m13_11_0_6_10
  · exact absurd hs (by decide)
  · exact m13_11_0_6_12

theorem m13_11_0_7_1 : go 13 7 9 [11, 0, 7, 1] = true := by decide +kernel
theorem m13_11_0_7_3 : go 13 7 9 [11, 0, 7, 3] = true := by decide +kernel
theorem m13_11_0_7_4 : go 13 7 9 [11, 0, 7, 4] = true := by decide +kernel
theorem m13_11_0_7_5 : go 13 7 9 [11, 0, 7, 5] = true := by decide +kernel
theorem m13_11_0_7_9 : go 13 7 9 [11, 0, 7, 9] = true := by decide +kernel
theorem m13_11_0_7_10 : go 13 7 9 [11, 0, 7, 10] = true := by decide +kernel
theorem m13_11_0_7_12 : go 13 7 9 [11, 0, 7, 12] = true := by decide +kernel

theorem m13_11_0_7 : go 13 7 10 [11, 0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_7_1
  · exact absurd hs (by decide)
  · exact m13_11_0_7_3
  · exact m13_11_0_7_4
  · exact m13_11_0_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_7_9
  · exact m13_11_0_7_10
  · exact absurd hs (by decide)
  · exact m13_11_0_7_12

theorem m13_11_0_8_1 : go 13 7 9 [11, 0, 8, 1] = true := by decide +kernel
theorem m13_11_0_8_3 : go 13 7 9 [11, 0, 8, 3] = true := by decide +kernel
theorem m13_11_0_8_4 : go 13 7 9 [11, 0, 8, 4] = true := by decide +kernel
theorem m13_11_0_8_5 : go 13 7 9 [11, 0, 8, 5] = true := by decide +kernel
theorem m13_11_0_8_6 : go 13 7 9 [11, 0, 8, 6] = true := by decide +kernel
theorem m13_11_0_8_10 : go 13 7 9 [11, 0, 8, 10] = true := by decide +kernel
theorem m13_11_0_8_12 : go 13 7 9 [11, 0, 8, 12] = true := by decide +kernel

theorem m13_11_0_8 : go 13 7 10 [11, 0, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_8_1
  · exact absurd hs (by decide)
  · exact m13_11_0_8_3
  · exact m13_11_0_8_4
  · exact m13_11_0_8_5
  · exact m13_11_0_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_8_10
  · exact absurd hs (by decide)
  · exact m13_11_0_8_12

theorem m13_11_0_10_1 : go 13 7 9 [11, 0, 10, 1] = true := by decide +kernel
theorem m13_11_0_10_3 : go 13 7 9 [11, 0, 10, 3] = true := by decide +kernel
theorem m13_11_0_10_4 : go 13 7 9 [11, 0, 10, 4] = true := by decide +kernel
theorem m13_11_0_10_5 : go 13 7 9 [11, 0, 10, 5] = true := by decide +kernel
theorem m13_11_0_10_6 : go 13 7 9 [11, 0, 10, 6] = true := by decide +kernel
theorem m13_11_0_10_7 : go 13 7 9 [11, 0, 10, 7] = true := by decide +kernel
theorem m13_11_0_10_12 : go 13 7 9 [11, 0, 10, 12] = true := by decide +kernel

theorem m13_11_0_10 : go 13 7 10 [11, 0, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_10_1
  · exact absurd hs (by decide)
  · exact m13_11_0_10_3
  · exact m13_11_0_10_4
  · exact m13_11_0_10_5
  · exact m13_11_0_10_6
  · exact m13_11_0_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_10_12

theorem m13_11_0_12_1 : go 13 7 9 [11, 0, 12, 1] = true := by decide +kernel
theorem m13_11_0_12_3 : go 13 7 9 [11, 0, 12, 3] = true := by decide +kernel
theorem m13_11_0_12_4 : go 13 7 9 [11, 0, 12, 4] = true := by decide +kernel
theorem m13_11_0_12_5 : go 13 7 9 [11, 0, 12, 5] = true := by decide +kernel
theorem m13_11_0_12_6 : go 13 7 9 [11, 0, 12, 6] = true := by decide +kernel
theorem m13_11_0_12_7 : go 13 7 9 [11, 0, 12, 7] = true := by decide +kernel
theorem m13_11_0_12_9 : go 13 7 9 [11, 0, 12, 9] = true := by decide +kernel
theorem m13_11_0_12_10 : go 13 7 9 [11, 0, 12, 10] = true := by decide +kernel

theorem m13_11_0_12 : go 13 7 10 [11, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_11_0_12_1
  · exact absurd hs (by decide)
  · exact m13_11_0_12_3
  · exact m13_11_0_12_4
  · exact m13_11_0_12_5
  · exact m13_11_0_12_6
  · exact m13_11_0_12_7
  · exact absurd hs (by decide)
  · exact m13_11_0_12_9
  · exact m13_11_0_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_11_0 : go 13 7 11 [11, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_0_2
  · exact m13_11_0_3
  · exact m13_11_0_4
  · exact m13_11_0_5
  · exact m13_11_0_6
  · exact m13_11_0_7
  · exact m13_11_0_8
  · exact absurd hs (by decide)
  · exact m13_11_0_10
  · exact absurd hs (by decide)
  · exact m13_11_0_12

end Misses
