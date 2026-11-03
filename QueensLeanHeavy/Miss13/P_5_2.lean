import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [5, 2]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_5_2_0_3 : go 13 7 9 [5, 2, 0, 3] = true := by decide +kernel
theorem m13_5_2_0_6 : go 13 7 9 [5, 2, 0, 6] = true := by decide +kernel
theorem m13_5_2_0_7 : go 13 7 9 [5, 2, 0, 7] = true := by decide +kernel
theorem m13_5_2_0_9 : go 13 7 9 [5, 2, 0, 9] = true := by decide +kernel
theorem m13_5_2_0_10 : go 13 7 9 [5, 2, 0, 10] = true := by decide +kernel
theorem m13_5_2_0_11 : go 13 7 9 [5, 2, 0, 11] = true := by decide +kernel
theorem m13_5_2_0_12 : go 13 7 9 [5, 2, 0, 12] = true := by decide +kernel

theorem m13_5_2_0 : go 13 7 10 [5, 2, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_0_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_0_6
  · exact m13_5_2_0_7
  · exact absurd hs (by decide)
  · exact m13_5_2_0_9
  · exact m13_5_2_0_10
  · exact m13_5_2_0_11
  · exact m13_5_2_0_12

theorem m13_5_2_4_1 : go 13 7 9 [5, 2, 4, 1] = true := by decide +kernel
theorem m13_5_2_4_6 : go 13 7 9 [5, 2, 4, 6] = true := by decide +kernel
theorem m13_5_2_4_7 : go 13 7 9 [5, 2, 4, 7] = true := by decide +kernel
theorem m13_5_2_4_9 : go 13 7 9 [5, 2, 4, 9] = true := by decide +kernel
theorem m13_5_2_4_10 : go 13 7 9 [5, 2, 4, 10] = true := by decide +kernel
theorem m13_5_2_4_11 : go 13 7 9 [5, 2, 4, 11] = true := by decide +kernel
theorem m13_5_2_4_12 : go 13 7 9 [5, 2, 4, 12] = true := by decide +kernel

theorem m13_5_2_4 : go 13 7 10 [5, 2, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_4_6
  · exact m13_5_2_4_7
  · exact absurd hs (by decide)
  · exact m13_5_2_4_9
  · exact m13_5_2_4_10
  · exact m13_5_2_4_11
  · exact m13_5_2_4_12

theorem m13_5_2_6_1 : go 13 7 9 [5, 2, 6, 1] = true := by decide +kernel
theorem m13_5_2_6_3 : go 13 7 9 [5, 2, 6, 3] = true := by decide +kernel
theorem m13_5_2_6_9 : go 13 7 9 [5, 2, 6, 9] = true := by decide +kernel
theorem m13_5_2_6_10 : go 13 7 9 [5, 2, 6, 10] = true := by decide +kernel
theorem m13_5_2_6_11 : go 13 7 9 [5, 2, 6, 11] = true := by decide +kernel
theorem m13_5_2_6_12 : go 13 7 9 [5, 2, 6, 12] = true := by decide +kernel

theorem m13_5_2_6 : go 13 7 10 [5, 2, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_6_1
  · exact absurd hs (by decide)
  · exact m13_5_2_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_6_9
  · exact m13_5_2_6_10
  · exact m13_5_2_6_11
  · exact m13_5_2_6_12

theorem m13_5_2_8_1 : go 13 7 9 [5, 2, 8, 1] = true := by decide +kernel
theorem m13_5_2_8_3 : go 13 7 9 [5, 2, 8, 3] = true := by decide +kernel
theorem m13_5_2_8_6 : go 13 7 9 [5, 2, 8, 6] = true := by decide +kernel
theorem m13_5_2_8_10 : go 13 7 9 [5, 2, 8, 10] = true := by decide +kernel
theorem m13_5_2_8_11 : go 13 7 9 [5, 2, 8, 11] = true := by decide +kernel
theorem m13_5_2_8_12 : go 13 7 9 [5, 2, 8, 12] = true := by decide +kernel

theorem m13_5_2_8 : go 13 7 10 [5, 2, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_8_1
  · exact absurd hs (by decide)
  · exact m13_5_2_8_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_8_10
  · exact m13_5_2_8_11
  · exact m13_5_2_8_12

theorem m13_5_2_9_1 : go 13 7 9 [5, 2, 9, 1] = true := by decide +kernel
theorem m13_5_2_9_3 : go 13 7 9 [5, 2, 9, 3] = true := by decide +kernel
theorem m13_5_2_9_6 : go 13 7 9 [5, 2, 9, 6] = true := by decide +kernel
theorem m13_5_2_9_7 : go 13 7 9 [5, 2, 9, 7] = true := by decide +kernel
theorem m13_5_2_9_11 : go 13 7 9 [5, 2, 9, 11] = true := by decide +kernel
theorem m13_5_2_9_12 : go 13 7 9 [5, 2, 9, 12] = true := by decide +kernel

theorem m13_5_2_9 : go 13 7 10 [5, 2, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_9_1
  · exact absurd hs (by decide)
  · exact m13_5_2_9_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_9_6
  · exact m13_5_2_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_9_11
  · exact m13_5_2_9_12

theorem m13_5_2_10_1 : go 13 7 9 [5, 2, 10, 1] = true := by decide +kernel
theorem m13_5_2_10_3 : go 13 7 9 [5, 2, 10, 3] = true := by decide +kernel
theorem m13_5_2_10_6 : go 13 7 9 [5, 2, 10, 6] = true := by decide +kernel
theorem m13_5_2_10_7 : go 13 7 9 [5, 2, 10, 7] = true := by decide +kernel
theorem m13_5_2_10_12 : go 13 7 9 [5, 2, 10, 12] = true := by decide +kernel

theorem m13_5_2_10 : go 13 7 10 [5, 2, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_10_1
  · exact absurd hs (by decide)
  · exact m13_5_2_10_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_10_6
  · exact m13_5_2_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_10_12

theorem m13_5_2_11_1 : go 13 7 9 [5, 2, 11, 1] = true := by decide +kernel
theorem m13_5_2_11_3 : go 13 7 9 [5, 2, 11, 3] = true := by decide +kernel
theorem m13_5_2_11_6 : go 13 7 9 [5, 2, 11, 6] = true := by decide +kernel
theorem m13_5_2_11_7 : go 13 7 9 [5, 2, 11, 7] = true := by decide +kernel
theorem m13_5_2_11_9 : go 13 7 9 [5, 2, 11, 9] = true := by decide +kernel

theorem m13_5_2_11 : go 13 7 10 [5, 2, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_11_1
  · exact absurd hs (by decide)
  · exact m13_5_2_11_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_11_6
  · exact m13_5_2_11_7
  · exact absurd hs (by decide)
  · exact m13_5_2_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_2_12_1 : go 13 7 9 [5, 2, 12, 1] = true := by decide +kernel
theorem m13_5_2_12_3 : go 13 7 9 [5, 2, 12, 3] = true := by decide +kernel
theorem m13_5_2_12_6 : go 13 7 9 [5, 2, 12, 6] = true := by decide +kernel
theorem m13_5_2_12_7 : go 13 7 9 [5, 2, 12, 7] = true := by decide +kernel
theorem m13_5_2_12_9 : go 13 7 9 [5, 2, 12, 9] = true := by decide +kernel
theorem m13_5_2_12_10 : go 13 7 9 [5, 2, 12, 10] = true := by decide +kernel

theorem m13_5_2_12 : go 13 7 10 [5, 2, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_2_12_1
  · exact absurd hs (by decide)
  · exact m13_5_2_12_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_12_6
  · exact m13_5_2_12_7
  · exact absurd hs (by decide)
  · exact m13_5_2_12_9
  · exact m13_5_2_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_2 : go 13 7 11 [5, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_2_4
  · exact absurd hs (by decide)
  · exact m13_5_2_6
  · exact absurd hs (by decide)
  · exact m13_5_2_8
  · exact m13_5_2_9
  · exact m13_5_2_10
  · exact m13_5_2_11
  · exact m13_5_2_12

end Misses
