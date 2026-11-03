import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [11, 4]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_11_4_0_3 : go 13 7 9 [11, 4, 0, 3] = true := by decide +kernel
theorem m13_11_4_0_5 : go 13 7 9 [11, 4, 0, 5] = true := by decide +kernel
theorem m13_11_4_0_7 : go 13 7 9 [11, 4, 0, 7] = true := by decide +kernel
theorem m13_11_4_0_9 : go 13 7 9 [11, 4, 0, 9] = true := by decide +kernel
theorem m13_11_4_0_10 : go 13 7 9 [11, 4, 0, 10] = true := by decide +kernel
theorem m13_11_4_0_12 : go 13 7 9 [11, 4, 0, 12] = true := by decide +kernel

theorem m13_11_4_0 : go 13 7 10 [11, 4, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_0_3
  · exact absurd hs (by decide)
  · exact m13_11_4_0_5
  · exact absurd hs (by decide)
  · exact m13_11_4_0_7
  · exact absurd hs (by decide)
  · exact m13_11_4_0_9
  · exact m13_11_4_0_10
  · exact absurd hs (by decide)
  · exact m13_11_4_0_12

theorem m13_11_4_1_3 : go 13 7 9 [11, 4, 1, 3] = true := by decide +kernel
theorem m13_11_4_1_5 : go 13 7 9 [11, 4, 1, 5] = true := by decide +kernel
theorem m13_11_4_1_7 : go 13 7 9 [11, 4, 1, 7] = true := by decide +kernel
theorem m13_11_4_1_9 : go 13 7 9 [11, 4, 1, 9] = true := by decide +kernel
theorem m13_11_4_1_10 : go 13 7 9 [11, 4, 1, 10] = true := by decide +kernel
theorem m13_11_4_1_12 : go 13 7 9 [11, 4, 1, 12] = true := by decide +kernel

theorem m13_11_4_1 : go 13 7 10 [11, 4, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_1_3
  · exact absurd hs (by decide)
  · exact m13_11_4_1_5
  · exact absurd hs (by decide)
  · exact m13_11_4_1_7
  · exact absurd hs (by decide)
  · exact m13_11_4_1_9
  · exact m13_11_4_1_10
  · exact absurd hs (by decide)
  · exact m13_11_4_1_12

theorem m13_11_4_2_0 : go 13 7 9 [11, 4, 2, 0] = true := by decide +kernel
theorem m13_11_4_2_5 : go 13 7 9 [11, 4, 2, 5] = true := by decide +kernel
theorem m13_11_4_2_7 : go 13 7 9 [11, 4, 2, 7] = true := by decide +kernel
theorem m13_11_4_2_9 : go 13 7 9 [11, 4, 2, 9] = true := by decide +kernel
theorem m13_11_4_2_10 : go 13 7 9 [11, 4, 2, 10] = true := by decide +kernel
theorem m13_11_4_2_12 : go 13 7 9 [11, 4, 2, 12] = true := by decide +kernel

theorem m13_11_4_2 : go 13 7 10 [11, 4, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_2_5
  · exact absurd hs (by decide)
  · exact m13_11_4_2_7
  · exact absurd hs (by decide)
  · exact m13_11_4_2_9
  · exact m13_11_4_2_10
  · exact absurd hs (by decide)
  · exact m13_11_4_2_12

theorem m13_11_4_6_0 : go 13 7 9 [11, 4, 6, 0] = true := by decide +kernel
theorem m13_11_4_6_1 : go 13 7 9 [11, 4, 6, 1] = true := by decide +kernel
theorem m13_11_4_6_3 : go 13 7 9 [11, 4, 6, 3] = true := by decide +kernel
theorem m13_11_4_6_9 : go 13 7 9 [11, 4, 6, 9] = true := by decide +kernel
theorem m13_11_4_6_10 : go 13 7 9 [11, 4, 6, 10] = true := by decide +kernel
theorem m13_11_4_6_12 : go 13 7 9 [11, 4, 6, 12] = true := by decide +kernel

theorem m13_11_4_6 : go 13 7 10 [11, 4, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_6_0
  · exact m13_11_4_6_1
  · exact absurd hs (by decide)
  · exact m13_11_4_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_6_9
  · exact m13_11_4_6_10
  · exact absurd hs (by decide)
  · exact m13_11_4_6_12

theorem m13_11_4_7_0 : go 13 7 9 [11, 4, 7, 0] = true := by decide +kernel
theorem m13_11_4_7_1 : go 13 7 9 [11, 4, 7, 1] = true := by decide +kernel
theorem m13_11_4_7_3 : go 13 7 9 [11, 4, 7, 3] = true := by decide +kernel
theorem m13_11_4_7_5 : go 13 7 9 [11, 4, 7, 5] = true := by decide +kernel
theorem m13_11_4_7_9 : go 13 7 9 [11, 4, 7, 9] = true := by decide +kernel
theorem m13_11_4_7_10 : go 13 7 9 [11, 4, 7, 10] = true := by decide +kernel
theorem m13_11_4_7_12 : go 13 7 9 [11, 4, 7, 12] = true := by decide +kernel

theorem m13_11_4_7 : go 13 7 10 [11, 4, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_7_0
  · exact m13_11_4_7_1
  · exact absurd hs (by decide)
  · exact m13_11_4_7_3
  · exact absurd hs (by decide)
  · exact m13_11_4_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_7_9
  · exact m13_11_4_7_10
  · exact absurd hs (by decide)
  · exact m13_11_4_7_12

theorem m13_11_4_8_0 : go 13 7 9 [11, 4, 8, 0] = true := by decide +kernel
theorem m13_11_4_8_1 : go 13 7 9 [11, 4, 8, 1] = true := by decide +kernel
theorem m13_11_4_8_3 : go 13 7 9 [11, 4, 8, 3] = true := by decide +kernel
theorem m13_11_4_8_5 : go 13 7 9 [11, 4, 8, 5] = true := by decide +kernel
theorem m13_11_4_8_10 : go 13 7 9 [11, 4, 8, 10] = true := by decide +kernel
theorem m13_11_4_8_12 : go 13 7 9 [11, 4, 8, 12] = true := by decide +kernel

theorem m13_11_4_8 : go 13 7 10 [11, 4, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_8_0
  · exact m13_11_4_8_1
  · exact absurd hs (by decide)
  · exact m13_11_4_8_3
  · exact absurd hs (by decide)
  · exact m13_11_4_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_8_10
  · exact absurd hs (by decide)
  · exact m13_11_4_8_12

theorem m13_11_4_10_0 : go 13 7 9 [11, 4, 10, 0] = true := by decide +kernel
theorem m13_11_4_10_1 : go 13 7 9 [11, 4, 10, 1] = true := by decide +kernel
theorem m13_11_4_10_3 : go 13 7 9 [11, 4, 10, 3] = true := by decide +kernel
theorem m13_11_4_10_5 : go 13 7 9 [11, 4, 10, 5] = true := by decide +kernel
theorem m13_11_4_10_7 : go 13 7 9 [11, 4, 10, 7] = true := by decide +kernel
theorem m13_11_4_10_12 : go 13 7 9 [11, 4, 10, 12] = true := by decide +kernel

theorem m13_11_4_10 : go 13 7 10 [11, 4, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_10_0
  · exact m13_11_4_10_1
  · exact absurd hs (by decide)
  · exact m13_11_4_10_3
  · exact absurd hs (by decide)
  · exact m13_11_4_10_5
  · exact absurd hs (by decide)
  · exact m13_11_4_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_10_12

theorem m13_11_4_12_0 : go 13 7 9 [11, 4, 12, 0] = true := by decide +kernel
theorem m13_11_4_12_1 : go 13 7 9 [11, 4, 12, 1] = true := by decide +kernel
theorem m13_11_4_12_3 : go 13 7 9 [11, 4, 12, 3] = true := by decide +kernel
theorem m13_11_4_12_5 : go 13 7 9 [11, 4, 12, 5] = true := by decide +kernel
theorem m13_11_4_12_7 : go 13 7 9 [11, 4, 12, 7] = true := by decide +kernel
theorem m13_11_4_12_9 : go 13 7 9 [11, 4, 12, 9] = true := by decide +kernel
theorem m13_11_4_12_10 : go 13 7 9 [11, 4, 12, 10] = true := by decide +kernel

theorem m13_11_4_12 : go 13 7 10 [11, 4, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_12_0
  · exact m13_11_4_12_1
  · exact absurd hs (by decide)
  · exact m13_11_4_12_3
  · exact absurd hs (by decide)
  · exact m13_11_4_12_5
  · exact absurd hs (by decide)
  · exact m13_11_4_12_7
  · exact absurd hs (by decide)
  · exact m13_11_4_12_9
  · exact m13_11_4_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_11_4 : go 13 7 11 [11, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_11_4_0
  · exact m13_11_4_1
  · exact m13_11_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_11_4_6
  · exact m13_11_4_7
  · exact m13_11_4_8
  · exact absurd hs (by decide)
  · exact m13_11_4_10
  · exact absurd hs (by decide)
  · exact m13_11_4_12

end Misses
