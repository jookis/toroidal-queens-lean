import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [1, 3]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_1_3_0_2 : go 13 7 9 [1, 3, 0, 2] = true := by decide +kernel
theorem m13_1_3_0_6 : go 13 7 9 [1, 3, 0, 6] = true := by decide +kernel
theorem m13_1_3_0_7 : go 13 7 9 [1, 3, 0, 7] = true := by decide +kernel
theorem m13_1_3_0_8 : go 13 7 9 [1, 3, 0, 8] = true := by decide +kernel
theorem m13_1_3_0_9 : go 13 7 9 [1, 3, 0, 9] = true := by decide +kernel
theorem m13_1_3_0_10 : go 13 7 9 [1, 3, 0, 10] = true := by decide +kernel
theorem m13_1_3_0_11 : go 13 7 9 [1, 3, 0, 11] = true := by decide +kernel
theorem m13_1_3_0_12 : go 13 7 9 [1, 3, 0, 12] = true := by decide +kernel

theorem m13_1_3_0 : go 13 7 10 [1, 3, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_0_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_0_6
  · exact m13_1_3_0_7
  · exact m13_1_3_0_8
  · exact m13_1_3_0_9
  · exact m13_1_3_0_10
  · exact m13_1_3_0_11
  · exact m13_1_3_0_12

theorem m13_1_3_5_0 : go 13 7 9 [1, 3, 5, 0] = true := by decide +kernel
theorem m13_1_3_5_2 : go 13 7 9 [1, 3, 5, 2] = true := by decide +kernel
theorem m13_1_3_5_7 : go 13 7 9 [1, 3, 5, 7] = true := by decide +kernel
theorem m13_1_3_5_8 : go 13 7 9 [1, 3, 5, 8] = true := by decide +kernel
theorem m13_1_3_5_9 : go 13 7 9 [1, 3, 5, 9] = true := by decide +kernel
theorem m13_1_3_5_10 : go 13 7 9 [1, 3, 5, 10] = true := by decide +kernel
theorem m13_1_3_5_11 : go 13 7 9 [1, 3, 5, 11] = true := by decide +kernel
theorem m13_1_3_5_12 : go 13 7 9 [1, 3, 5, 12] = true := by decide +kernel

theorem m13_1_3_5 : go 13 7 10 [1, 3, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_5_0
  · exact absurd hs (by decide)
  · exact m13_1_3_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_5_7
  · exact m13_1_3_5_8
  · exact m13_1_3_5_9
  · exact m13_1_3_5_10
  · exact m13_1_3_5_11
  · exact m13_1_3_5_12

theorem m13_1_3_6_0 : go 13 7 9 [1, 3, 6, 0] = true := by decide +kernel
theorem m13_1_3_6_2 : go 13 7 9 [1, 3, 6, 2] = true := by decide +kernel
theorem m13_1_3_6_8 : go 13 7 9 [1, 3, 6, 8] = true := by decide +kernel
theorem m13_1_3_6_9 : go 13 7 9 [1, 3, 6, 9] = true := by decide +kernel
theorem m13_1_3_6_10 : go 13 7 9 [1, 3, 6, 10] = true := by decide +kernel
theorem m13_1_3_6_11 : go 13 7 9 [1, 3, 6, 11] = true := by decide +kernel
theorem m13_1_3_6_12 : go 13 7 9 [1, 3, 6, 12] = true := by decide +kernel

theorem m13_1_3_6 : go 13 7 10 [1, 3, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_6_0
  · exact absurd hs (by decide)
  · exact m13_1_3_6_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_6_8
  · exact m13_1_3_6_9
  · exact m13_1_3_6_10
  · exact m13_1_3_6_11
  · exact m13_1_3_6_12

theorem m13_1_3_7_0 : go 13 7 9 [1, 3, 7, 0] = true := by decide +kernel
theorem m13_1_3_7_2 : go 13 7 9 [1, 3, 7, 2] = true := by decide +kernel
theorem m13_1_3_7_9 : go 13 7 9 [1, 3, 7, 9] = true := by decide +kernel
theorem m13_1_3_7_10 : go 13 7 9 [1, 3, 7, 10] = true := by decide +kernel
theorem m13_1_3_7_11 : go 13 7 9 [1, 3, 7, 11] = true := by decide +kernel
theorem m13_1_3_7_12 : go 13 7 9 [1, 3, 7, 12] = true := by decide +kernel

theorem m13_1_3_7 : go 13 7 10 [1, 3, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_7_0
  · exact absurd hs (by decide)
  · exact m13_1_3_7_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_7_9
  · exact m13_1_3_7_10
  · exact m13_1_3_7_11
  · exact m13_1_3_7_12

theorem m13_1_3_8_0 : go 13 7 9 [1, 3, 8, 0] = true := by decide +kernel
theorem m13_1_3_8_2 : go 13 7 9 [1, 3, 8, 2] = true := by decide +kernel
theorem m13_1_3_8_6 : go 13 7 9 [1, 3, 8, 6] = true := by decide +kernel
theorem m13_1_3_8_10 : go 13 7 9 [1, 3, 8, 10] = true := by decide +kernel
theorem m13_1_3_8_11 : go 13 7 9 [1, 3, 8, 11] = true := by decide +kernel
theorem m13_1_3_8_12 : go 13 7 9 [1, 3, 8, 12] = true := by decide +kernel

theorem m13_1_3_8 : go 13 7 10 [1, 3, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_8_0
  · exact absurd hs (by decide)
  · exact m13_1_3_8_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_8_10
  · exact m13_1_3_8_11
  · exact m13_1_3_8_12

theorem m13_1_3_9_0 : go 13 7 9 [1, 3, 9, 0] = true := by decide +kernel
theorem m13_1_3_9_2 : go 13 7 9 [1, 3, 9, 2] = true := by decide +kernel
theorem m13_1_3_9_6 : go 13 7 9 [1, 3, 9, 6] = true := by decide +kernel
theorem m13_1_3_9_7 : go 13 7 9 [1, 3, 9, 7] = true := by decide +kernel
theorem m13_1_3_9_11 : go 13 7 9 [1, 3, 9, 11] = true := by decide +kernel
theorem m13_1_3_9_12 : go 13 7 9 [1, 3, 9, 12] = true := by decide +kernel

theorem m13_1_3_9 : go 13 7 10 [1, 3, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_9_0
  · exact absurd hs (by decide)
  · exact m13_1_3_9_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_9_6
  · exact m13_1_3_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_9_11
  · exact m13_1_3_9_12

theorem m13_1_3_10_0 : go 13 7 9 [1, 3, 10, 0] = true := by decide +kernel
theorem m13_1_3_10_2 : go 13 7 9 [1, 3, 10, 2] = true := by decide +kernel
theorem m13_1_3_10_6 : go 13 7 9 [1, 3, 10, 6] = true := by decide +kernel
theorem m13_1_3_10_7 : go 13 7 9 [1, 3, 10, 7] = true := by decide +kernel
theorem m13_1_3_10_8 : go 13 7 9 [1, 3, 10, 8] = true := by decide +kernel
theorem m13_1_3_10_12 : go 13 7 9 [1, 3, 10, 12] = true := by decide +kernel

theorem m13_1_3_10 : go 13 7 10 [1, 3, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_10_0
  · exact absurd hs (by decide)
  · exact m13_1_3_10_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_10_6
  · exact m13_1_3_10_7
  · exact m13_1_3_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_10_12

theorem m13_1_3_11_0 : go 13 7 9 [1, 3, 11, 0] = true := by decide +kernel
theorem m13_1_3_11_2 : go 13 7 9 [1, 3, 11, 2] = true := by decide +kernel
theorem m13_1_3_11_6 : go 13 7 9 [1, 3, 11, 6] = true := by decide +kernel
theorem m13_1_3_11_7 : go 13 7 9 [1, 3, 11, 7] = true := by decide +kernel
theorem m13_1_3_11_8 : go 13 7 9 [1, 3, 11, 8] = true := by decide +kernel
theorem m13_1_3_11_9 : go 13 7 9 [1, 3, 11, 9] = true := by decide +kernel

theorem m13_1_3_11 : go 13 7 10 [1, 3, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_11_0
  · exact absurd hs (by decide)
  · exact m13_1_3_11_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_11_6
  · exact m13_1_3_11_7
  · exact m13_1_3_11_8
  · exact m13_1_3_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_3_12_0 : go 13 7 9 [1, 3, 12, 0] = true := by decide +kernel
theorem m13_1_3_12_2 : go 13 7 9 [1, 3, 12, 2] = true := by decide +kernel
theorem m13_1_3_12_6 : go 13 7 9 [1, 3, 12, 6] = true := by decide +kernel
theorem m13_1_3_12_7 : go 13 7 9 [1, 3, 12, 7] = true := by decide +kernel
theorem m13_1_3_12_8 : go 13 7 9 [1, 3, 12, 8] = true := by decide +kernel
theorem m13_1_3_12_9 : go 13 7 9 [1, 3, 12, 9] = true := by decide +kernel
theorem m13_1_3_12_10 : go 13 7 9 [1, 3, 12, 10] = true := by decide +kernel

theorem m13_1_3_12 : go 13 7 10 [1, 3, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_12_0
  · exact absurd hs (by decide)
  · exact m13_1_3_12_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_12_6
  · exact m13_1_3_12_7
  · exact m13_1_3_12_8
  · exact m13_1_3_12_9
  · exact m13_1_3_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_1_3 : go 13 7 11 [1, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_1_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_1_3_5
  · exact m13_1_3_6
  · exact m13_1_3_7
  · exact m13_1_3_8
  · exact m13_1_3_9
  · exact m13_1_3_10
  · exact m13_1_3_11
  · exact m13_1_3_12

end Misses
