import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [2, 6]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_2_6_1_3 : go 13 7 9 [2, 6, 1, 3] = true := by decide +kernel
theorem m13_2_6_1_7 : go 13 7 9 [2, 6, 1, 7] = true := by decide +kernel
theorem m13_2_6_1_9 : go 13 7 9 [2, 6, 1, 9] = true := by decide +kernel
theorem m13_2_6_1_10 : go 13 7 9 [2, 6, 1, 10] = true := by decide +kernel
theorem m13_2_6_1_11 : go 13 7 9 [2, 6, 1, 11] = true := by decide +kernel
theorem m13_2_6_1_12 : go 13 7 9 [2, 6, 1, 12] = true := by decide +kernel

theorem m13_2_6_1 : go 13 7 10 [2, 6, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_1_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_1_7
  · exact absurd hs (by decide)
  · exact m13_2_6_1_9
  · exact m13_2_6_1_10
  · exact m13_2_6_1_11
  · exact m13_2_6_1_12

theorem m13_2_6_3_0 : go 13 7 9 [2, 6, 3, 0] = true := by decide +kernel
theorem m13_2_6_3_1 : go 13 7 9 [2, 6, 3, 1] = true := by decide +kernel
theorem m13_2_6_3_7 : go 13 7 9 [2, 6, 3, 7] = true := by decide +kernel
theorem m13_2_6_3_9 : go 13 7 9 [2, 6, 3, 9] = true := by decide +kernel
theorem m13_2_6_3_10 : go 13 7 9 [2, 6, 3, 10] = true := by decide +kernel
theorem m13_2_6_3_11 : go 13 7 9 [2, 6, 3, 11] = true := by decide +kernel
theorem m13_2_6_3_12 : go 13 7 9 [2, 6, 3, 12] = true := by decide +kernel

theorem m13_2_6_3 : go 13 7 10 [2, 6, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_6_3_0
  · exact m13_2_6_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_3_7
  · exact absurd hs (by decide)
  · exact m13_2_6_3_9
  · exact m13_2_6_3_10
  · exact m13_2_6_3_11
  · exact m13_2_6_3_12

theorem m13_2_6_8_0 : go 13 7 9 [2, 6, 8, 0] = true := by decide +kernel
theorem m13_2_6_8_1 : go 13 7 9 [2, 6, 8, 1] = true := by decide +kernel
theorem m13_2_6_8_3 : go 13 7 9 [2, 6, 8, 3] = true := by decide +kernel
theorem m13_2_6_8_10 : go 13 7 9 [2, 6, 8, 10] = true := by decide +kernel
theorem m13_2_6_8_11 : go 13 7 9 [2, 6, 8, 11] = true := by decide +kernel
theorem m13_2_6_8_12 : go 13 7 9 [2, 6, 8, 12] = true := by decide +kernel

theorem m13_2_6_8 : go 13 7 10 [2, 6, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_6_8_0
  · exact m13_2_6_8_1
  · exact absurd hs (by decide)
  · exact m13_2_6_8_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_8_10
  · exact m13_2_6_8_11
  · exact m13_2_6_8_12

theorem m13_2_6_9_0 : go 13 7 9 [2, 6, 9, 0] = true := by decide +kernel
theorem m13_2_6_9_1 : go 13 7 9 [2, 6, 9, 1] = true := by decide +kernel
theorem m13_2_6_9_3 : go 13 7 9 [2, 6, 9, 3] = true := by decide +kernel
theorem m13_2_6_9_7 : go 13 7 9 [2, 6, 9, 7] = true := by decide +kernel
theorem m13_2_6_9_11 : go 13 7 9 [2, 6, 9, 11] = true := by decide +kernel
theorem m13_2_6_9_12 : go 13 7 9 [2, 6, 9, 12] = true := by decide +kernel

theorem m13_2_6_9 : go 13 7 10 [2, 6, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_6_9_0
  · exact m13_2_6_9_1
  · exact absurd hs (by decide)
  · exact m13_2_6_9_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_9_11
  · exact m13_2_6_9_12

theorem m13_2_6_10_0 : go 13 7 9 [2, 6, 10, 0] = true := by decide +kernel
theorem m13_2_6_10_1 : go 13 7 9 [2, 6, 10, 1] = true := by decide +kernel
theorem m13_2_6_10_3 : go 13 7 9 [2, 6, 10, 3] = true := by decide +kernel
theorem m13_2_6_10_7 : go 13 7 9 [2, 6, 10, 7] = true := by decide +kernel
theorem m13_2_6_10_12 : go 13 7 9 [2, 6, 10, 12] = true := by decide +kernel

theorem m13_2_6_10 : go 13 7 10 [2, 6, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_6_10_0
  · exact m13_2_6_10_1
  · exact absurd hs (by decide)
  · exact m13_2_6_10_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_10_12

theorem m13_2_6_11_0 : go 13 7 9 [2, 6, 11, 0] = true := by decide +kernel
theorem m13_2_6_11_1 : go 13 7 9 [2, 6, 11, 1] = true := by decide +kernel
theorem m13_2_6_11_3 : go 13 7 9 [2, 6, 11, 3] = true := by decide +kernel
theorem m13_2_6_11_7 : go 13 7 9 [2, 6, 11, 7] = true := by decide +kernel
theorem m13_2_6_11_9 : go 13 7 9 [2, 6, 11, 9] = true := by decide +kernel

theorem m13_2_6_11 : go 13 7 10 [2, 6, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_6_11_0
  · exact m13_2_6_11_1
  · exact absurd hs (by decide)
  · exact m13_2_6_11_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_11_7
  · exact absurd hs (by decide)
  · exact m13_2_6_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_6_12_0 : go 13 7 9 [2, 6, 12, 0] = true := by decide +kernel
theorem m13_2_6_12_1 : go 13 7 9 [2, 6, 12, 1] = true := by decide +kernel
theorem m13_2_6_12_3 : go 13 7 9 [2, 6, 12, 3] = true := by decide +kernel
theorem m13_2_6_12_7 : go 13 7 9 [2, 6, 12, 7] = true := by decide +kernel
theorem m13_2_6_12_9 : go 13 7 9 [2, 6, 12, 9] = true := by decide +kernel
theorem m13_2_6_12_10 : go 13 7 9 [2, 6, 12, 10] = true := by decide +kernel

theorem m13_2_6_12 : go 13 7 10 [2, 6, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_2_6_12_0
  · exact m13_2_6_12_1
  · exact absurd hs (by decide)
  · exact m13_2_6_12_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_12_7
  · exact absurd hs (by decide)
  · exact m13_2_6_12_9
  · exact m13_2_6_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_2_6 : go 13 7 11 [2, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_2_6_1
  · exact absurd hs (by decide)
  · exact m13_2_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_2_6_8
  · exact m13_2_6_9
  · exact m13_2_6_10
  · exact m13_2_6_11
  · exact m13_2_6_12

end Misses
