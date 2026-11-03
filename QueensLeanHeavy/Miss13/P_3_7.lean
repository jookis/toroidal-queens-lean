import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 7]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_7_0_2 : go 13 7 9 [3, 7, 0, 2] = true := by decide +kernel
theorem m13_3_7_0_4 : go 13 7 9 [3, 7, 0, 4] = true := by decide +kernel
theorem m13_3_7_0_8 : go 13 7 9 [3, 7, 0, 8] = true := by decide +kernel
theorem m13_3_7_0_10 : go 13 7 9 [3, 7, 0, 10] = true := by decide +kernel
theorem m13_3_7_0_11 : go 13 7 9 [3, 7, 0, 11] = true := by decide +kernel
theorem m13_3_7_0_12 : go 13 7 9 [3, 7, 0, 12] = true := by decide +kernel

theorem m13_3_7_0 : go 13 7 10 [3, 7, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_0_2
  · exact absurd hs (by decide)
  · exact m13_3_7_0_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_0_8
  · exact absurd hs (by decide)
  · exact m13_3_7_0_10
  · exact m13_3_7_0_11
  · exact m13_3_7_0_12

theorem m13_3_7_2_4 : go 13 7 9 [3, 7, 2, 4] = true := by decide +kernel
theorem m13_3_7_2_8 : go 13 7 9 [3, 7, 2, 8] = true := by decide +kernel
theorem m13_3_7_2_10 : go 13 7 9 [3, 7, 2, 10] = true := by decide +kernel
theorem m13_3_7_2_11 : go 13 7 9 [3, 7, 2, 11] = true := by decide +kernel
theorem m13_3_7_2_12 : go 13 7 9 [3, 7, 2, 12] = true := by decide +kernel

theorem m13_3_7_2 : go 13 7 10 [3, 7, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_2_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_2_8
  · exact absurd hs (by decide)
  · exact m13_3_7_2_10
  · exact m13_3_7_2_11
  · exact m13_3_7_2_12

theorem m13_3_7_4_1 : go 13 7 9 [3, 7, 4, 1] = true := by decide +kernel
theorem m13_3_7_4_2 : go 13 7 9 [3, 7, 4, 2] = true := by decide +kernel
theorem m13_3_7_4_8 : go 13 7 9 [3, 7, 4, 8] = true := by decide +kernel
theorem m13_3_7_4_10 : go 13 7 9 [3, 7, 4, 10] = true := by decide +kernel
theorem m13_3_7_4_11 : go 13 7 9 [3, 7, 4, 11] = true := by decide +kernel
theorem m13_3_7_4_12 : go 13 7 9 [3, 7, 4, 12] = true := by decide +kernel

theorem m13_3_7_4 : go 13 7 10 [3, 7, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_7_4_1
  · exact m13_3_7_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_4_8
  · exact absurd hs (by decide)
  · exact m13_3_7_4_10
  · exact m13_3_7_4_11
  · exact m13_3_7_4_12

theorem m13_3_7_9_1 : go 13 7 9 [3, 7, 9, 1] = true := by decide +kernel
theorem m13_3_7_9_2 : go 13 7 9 [3, 7, 9, 2] = true := by decide +kernel
theorem m13_3_7_9_4 : go 13 7 9 [3, 7, 9, 4] = true := by decide +kernel
theorem m13_3_7_9_11 : go 13 7 9 [3, 7, 9, 11] = true := by decide +kernel
theorem m13_3_7_9_12 : go 13 7 9 [3, 7, 9, 12] = true := by decide +kernel

theorem m13_3_7_9 : go 13 7 10 [3, 7, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_7_9_1
  · exact m13_3_7_9_2
  · exact absurd hs (by decide)
  · exact m13_3_7_9_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_9_11
  · exact m13_3_7_9_12

theorem m13_3_7_10_1 : go 13 7 9 [3, 7, 10, 1] = true := by decide +kernel
theorem m13_3_7_10_2 : go 13 7 9 [3, 7, 10, 2] = true := by decide +kernel
theorem m13_3_7_10_4 : go 13 7 9 [3, 7, 10, 4] = true := by decide +kernel
theorem m13_3_7_10_8 : go 13 7 9 [3, 7, 10, 8] = true := by decide +kernel
theorem m13_3_7_10_12 : go 13 7 9 [3, 7, 10, 12] = true := by decide +kernel

theorem m13_3_7_10 : go 13 7 10 [3, 7, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_7_10_1
  · exact m13_3_7_10_2
  · exact absurd hs (by decide)
  · exact m13_3_7_10_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_10_12

theorem m13_3_7_11_1 : go 13 7 9 [3, 7, 11, 1] = true := by decide +kernel
theorem m13_3_7_11_2 : go 13 7 9 [3, 7, 11, 2] = true := by decide +kernel
theorem m13_3_7_11_4 : go 13 7 9 [3, 7, 11, 4] = true := by decide +kernel
theorem m13_3_7_11_8 : go 13 7 9 [3, 7, 11, 8] = true := by decide +kernel

theorem m13_3_7_11 : go 13 7 10 [3, 7, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_7_11_1
  · exact m13_3_7_11_2
  · exact absurd hs (by decide)
  · exact m13_3_7_11_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_7_12_1 : go 13 7 9 [3, 7, 12, 1] = true := by decide +kernel
theorem m13_3_7_12_2 : go 13 7 9 [3, 7, 12, 2] = true := by decide +kernel
theorem m13_3_7_12_4 : go 13 7 9 [3, 7, 12, 4] = true := by decide +kernel
theorem m13_3_7_12_8 : go 13 7 9 [3, 7, 12, 8] = true := by decide +kernel
theorem m13_3_7_12_10 : go 13 7 9 [3, 7, 12, 10] = true := by decide +kernel

theorem m13_3_7_12 : go 13 7 10 [3, 7, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_7_12_1
  · exact m13_3_7_12_2
  · exact absurd hs (by decide)
  · exact m13_3_7_12_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_12_8
  · exact absurd hs (by decide)
  · exact m13_3_7_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_7 : go 13 7 11 [3, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_3_7_0
  · exact absurd hs (by decide)
  · exact m13_3_7_2
  · exact absurd hs (by decide)
  · exact m13_3_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_7_9
  · exact m13_3_7_10
  · exact m13_3_7_11
  · exact m13_3_7_12

end Misses
