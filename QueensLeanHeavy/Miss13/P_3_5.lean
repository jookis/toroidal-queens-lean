import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 5]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_5_0_2 : go 13 7 9 [3, 5, 0, 2] = true := by decide +kernel
theorem m13_3_5_0_4 : go 13 7 9 [3, 5, 0, 4] = true := by decide +kernel
theorem m13_3_5_0_8 : go 13 7 9 [3, 5, 0, 8] = true := by decide +kernel
theorem m13_3_5_0_9 : go 13 7 9 [3, 5, 0, 9] = true := by decide +kernel
theorem m13_3_5_0_10 : go 13 7 9 [3, 5, 0, 10] = true := by decide +kernel
theorem m13_3_5_0_11 : go 13 7 9 [3, 5, 0, 11] = true := by decide +kernel
theorem m13_3_5_0_12 : go 13 7 9 [3, 5, 0, 12] = true := by decide +kernel

theorem m13_3_5_0 : go 13 7 10 [3, 5, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_0_2
  · exact absurd hs (by decide)
  · exact m13_3_5_0_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_0_8
  · exact m13_3_5_0_9
  · exact m13_3_5_0_10
  · exact m13_3_5_0_11
  · exact m13_3_5_0_12

theorem m13_3_5_2_4 : go 13 7 9 [3, 5, 2, 4] = true := by decide +kernel
theorem m13_3_5_2_8 : go 13 7 9 [3, 5, 2, 8] = true := by decide +kernel
theorem m13_3_5_2_9 : go 13 7 9 [3, 5, 2, 9] = true := by decide +kernel
theorem m13_3_5_2_10 : go 13 7 9 [3, 5, 2, 10] = true := by decide +kernel
theorem m13_3_5_2_11 : go 13 7 9 [3, 5, 2, 11] = true := by decide +kernel
theorem m13_3_5_2_12 : go 13 7 9 [3, 5, 2, 12] = true := by decide +kernel

theorem m13_3_5_2 : go 13 7 10 [3, 5, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_2_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_2_8
  · exact m13_3_5_2_9
  · exact m13_3_5_2_10
  · exact m13_3_5_2_11
  · exact m13_3_5_2_12

theorem m13_3_5_7_1 : go 13 7 9 [3, 5, 7, 1] = true := by decide +kernel
theorem m13_3_5_7_2 : go 13 7 9 [3, 5, 7, 2] = true := by decide +kernel
theorem m13_3_5_7_4 : go 13 7 9 [3, 5, 7, 4] = true := by decide +kernel
theorem m13_3_5_7_9 : go 13 7 9 [3, 5, 7, 9] = true := by decide +kernel
theorem m13_3_5_7_10 : go 13 7 9 [3, 5, 7, 10] = true := by decide +kernel
theorem m13_3_5_7_11 : go 13 7 9 [3, 5, 7, 11] = true := by decide +kernel
theorem m13_3_5_7_12 : go 13 7 9 [3, 5, 7, 12] = true := by decide +kernel

theorem m13_3_5_7 : go 13 7 10 [3, 5, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_5_7_1
  · exact m13_3_5_7_2
  · exact absurd hs (by decide)
  · exact m13_3_5_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_7_9
  · exact m13_3_5_7_10
  · exact m13_3_5_7_11
  · exact m13_3_5_7_12

theorem m13_3_5_8_1 : go 13 7 9 [3, 5, 8, 1] = true := by decide +kernel
theorem m13_3_5_8_2 : go 13 7 9 [3, 5, 8, 2] = true := by decide +kernel
theorem m13_3_5_8_4 : go 13 7 9 [3, 5, 8, 4] = true := by decide +kernel
theorem m13_3_5_8_10 : go 13 7 9 [3, 5, 8, 10] = true := by decide +kernel
theorem m13_3_5_8_11 : go 13 7 9 [3, 5, 8, 11] = true := by decide +kernel
theorem m13_3_5_8_12 : go 13 7 9 [3, 5, 8, 12] = true := by decide +kernel

theorem m13_3_5_8 : go 13 7 10 [3, 5, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_5_8_1
  · exact m13_3_5_8_2
  · exact absurd hs (by decide)
  · exact m13_3_5_8_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_8_10
  · exact m13_3_5_8_11
  · exact m13_3_5_8_12

theorem m13_3_5_9_1 : go 13 7 9 [3, 5, 9, 1] = true := by decide +kernel
theorem m13_3_5_9_2 : go 13 7 9 [3, 5, 9, 2] = true := by decide +kernel
theorem m13_3_5_9_4 : go 13 7 9 [3, 5, 9, 4] = true := by decide +kernel
theorem m13_3_5_9_11 : go 13 7 9 [3, 5, 9, 11] = true := by decide +kernel
theorem m13_3_5_9_12 : go 13 7 9 [3, 5, 9, 12] = true := by decide +kernel

theorem m13_3_5_9 : go 13 7 10 [3, 5, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_5_9_1
  · exact m13_3_5_9_2
  · exact absurd hs (by decide)
  · exact m13_3_5_9_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_9_11
  · exact m13_3_5_9_12

theorem m13_3_5_10_1 : go 13 7 9 [3, 5, 10, 1] = true := by decide +kernel
theorem m13_3_5_10_2 : go 13 7 9 [3, 5, 10, 2] = true := by decide +kernel
theorem m13_3_5_10_4 : go 13 7 9 [3, 5, 10, 4] = true := by decide +kernel
theorem m13_3_5_10_8 : go 13 7 9 [3, 5, 10, 8] = true := by decide +kernel
theorem m13_3_5_10_12 : go 13 7 9 [3, 5, 10, 12] = true := by decide +kernel

theorem m13_3_5_10 : go 13 7 10 [3, 5, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_5_10_1
  · exact m13_3_5_10_2
  · exact absurd hs (by decide)
  · exact m13_3_5_10_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_10_12

theorem m13_3_5_11_1 : go 13 7 9 [3, 5, 11, 1] = true := by decide +kernel
theorem m13_3_5_11_2 : go 13 7 9 [3, 5, 11, 2] = true := by decide +kernel
theorem m13_3_5_11_4 : go 13 7 9 [3, 5, 11, 4] = true := by decide +kernel
theorem m13_3_5_11_8 : go 13 7 9 [3, 5, 11, 8] = true := by decide +kernel
theorem m13_3_5_11_9 : go 13 7 9 [3, 5, 11, 9] = true := by decide +kernel

theorem m13_3_5_11 : go 13 7 10 [3, 5, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_5_11_1
  · exact m13_3_5_11_2
  · exact absurd hs (by decide)
  · exact m13_3_5_11_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_11_8
  · exact m13_3_5_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_5_12_1 : go 13 7 9 [3, 5, 12, 1] = true := by decide +kernel
theorem m13_3_5_12_2 : go 13 7 9 [3, 5, 12, 2] = true := by decide +kernel
theorem m13_3_5_12_4 : go 13 7 9 [3, 5, 12, 4] = true := by decide +kernel
theorem m13_3_5_12_8 : go 13 7 9 [3, 5, 12, 8] = true := by decide +kernel
theorem m13_3_5_12_9 : go 13 7 9 [3, 5, 12, 9] = true := by decide +kernel
theorem m13_3_5_12_10 : go 13 7 9 [3, 5, 12, 10] = true := by decide +kernel

theorem m13_3_5_12 : go 13 7 10 [3, 5, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_5_12_1
  · exact m13_3_5_12_2
  · exact absurd hs (by decide)
  · exact m13_3_5_12_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_12_8
  · exact m13_3_5_12_9
  · exact m13_3_5_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_5 : go 13 7 11 [3, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_3_5_0
  · exact absurd hs (by decide)
  · exact m13_3_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_5_7
  · exact m13_3_5_8
  · exact m13_3_5_9
  · exact m13_3_5_10
  · exact m13_3_5_11
  · exact m13_3_5_12

end Misses
