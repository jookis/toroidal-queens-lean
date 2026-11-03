import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [5, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_5_0_2_4 : go 13 7 9 [5, 0, 2, 4] = true := by decide +kernel
theorem m13_5_0_2_6 : go 13 7 9 [5, 0, 2, 6] = true := by decide +kernel
theorem m13_5_0_2_7 : go 13 7 9 [5, 0, 2, 7] = true := by decide +kernel
theorem m13_5_0_2_9 : go 13 7 9 [5, 0, 2, 9] = true := by decide +kernel
theorem m13_5_0_2_10 : go 13 7 9 [5, 0, 2, 10] = true := by decide +kernel
theorem m13_5_0_2_11 : go 13 7 9 [5, 0, 2, 11] = true := by decide +kernel
theorem m13_5_0_2_12 : go 13 7 9 [5, 0, 2, 12] = true := by decide +kernel

theorem m13_5_0_2 : go 13 7 10 [5, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_2_4
  · exact absurd hs (by decide)
  · exact m13_5_0_2_6
  · exact m13_5_0_2_7
  · exact absurd hs (by decide)
  · exact m13_5_0_2_9
  · exact m13_5_0_2_10
  · exact m13_5_0_2_11
  · exact m13_5_0_2_12

theorem m13_5_0_4_1 : go 13 7 9 [5, 0, 4, 1] = true := by decide +kernel
theorem m13_5_0_4_6 : go 13 7 9 [5, 0, 4, 6] = true := by decide +kernel
theorem m13_5_0_4_7 : go 13 7 9 [5, 0, 4, 7] = true := by decide +kernel
theorem m13_5_0_4_9 : go 13 7 9 [5, 0, 4, 9] = true := by decide +kernel
theorem m13_5_0_4_10 : go 13 7 9 [5, 0, 4, 10] = true := by decide +kernel
theorem m13_5_0_4_11 : go 13 7 9 [5, 0, 4, 11] = true := by decide +kernel
theorem m13_5_0_4_12 : go 13 7 9 [5, 0, 4, 12] = true := by decide +kernel

theorem m13_5_0_4 : go 13 7 10 [5, 0, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_4_6
  · exact m13_5_0_4_7
  · exact absurd hs (by decide)
  · exact m13_5_0_4_9
  · exact m13_5_0_4_10
  · exact m13_5_0_4_11
  · exact m13_5_0_4_12

theorem m13_5_0_6_1 : go 13 7 9 [5, 0, 6, 1] = true := by decide +kernel
theorem m13_5_0_6_3 : go 13 7 9 [5, 0, 6, 3] = true := by decide +kernel
theorem m13_5_0_6_4 : go 13 7 9 [5, 0, 6, 4] = true := by decide +kernel
theorem m13_5_0_6_9 : go 13 7 9 [5, 0, 6, 9] = true := by decide +kernel
theorem m13_5_0_6_10 : go 13 7 9 [5, 0, 6, 10] = true := by decide +kernel
theorem m13_5_0_6_11 : go 13 7 9 [5, 0, 6, 11] = true := by decide +kernel
theorem m13_5_0_6_12 : go 13 7 9 [5, 0, 6, 12] = true := by decide +kernel

theorem m13_5_0_6 : go 13 7 10 [5, 0, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_6_1
  · exact absurd hs (by decide)
  · exact m13_5_0_6_3
  · exact m13_5_0_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_6_9
  · exact m13_5_0_6_10
  · exact m13_5_0_6_11
  · exact m13_5_0_6_12

theorem m13_5_0_8_1 : go 13 7 9 [5, 0, 8, 1] = true := by decide +kernel
theorem m13_5_0_8_3 : go 13 7 9 [5, 0, 8, 3] = true := by decide +kernel
theorem m13_5_0_8_4 : go 13 7 9 [5, 0, 8, 4] = true := by decide +kernel
theorem m13_5_0_8_6 : go 13 7 9 [5, 0, 8, 6] = true := by decide +kernel
theorem m13_5_0_8_10 : go 13 7 9 [5, 0, 8, 10] = true := by decide +kernel
theorem m13_5_0_8_11 : go 13 7 9 [5, 0, 8, 11] = true := by decide +kernel
theorem m13_5_0_8_12 : go 13 7 9 [5, 0, 8, 12] = true := by decide +kernel

theorem m13_5_0_8 : go 13 7 10 [5, 0, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_8_1
  · exact absurd hs (by decide)
  · exact m13_5_0_8_3
  · exact m13_5_0_8_4
  · exact absurd hs (by decide)
  · exact m13_5_0_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_8_10
  · exact m13_5_0_8_11
  · exact m13_5_0_8_12

theorem m13_5_0_9_1 : go 13 7 9 [5, 0, 9, 1] = true := by decide +kernel
theorem m13_5_0_9_3 : go 13 7 9 [5, 0, 9, 3] = true := by decide +kernel
theorem m13_5_0_9_4 : go 13 7 9 [5, 0, 9, 4] = true := by decide +kernel
theorem m13_5_0_9_6 : go 13 7 9 [5, 0, 9, 6] = true := by decide +kernel
theorem m13_5_0_9_7 : go 13 7 9 [5, 0, 9, 7] = true := by decide +kernel
theorem m13_5_0_9_11 : go 13 7 9 [5, 0, 9, 11] = true := by decide +kernel
theorem m13_5_0_9_12 : go 13 7 9 [5, 0, 9, 12] = true := by decide +kernel

theorem m13_5_0_9 : go 13 7 10 [5, 0, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_9_1
  · exact absurd hs (by decide)
  · exact m13_5_0_9_3
  · exact m13_5_0_9_4
  · exact absurd hs (by decide)
  · exact m13_5_0_9_6
  · exact m13_5_0_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_9_11
  · exact m13_5_0_9_12

theorem m13_5_0_10_1 : go 13 7 9 [5, 0, 10, 1] = true := by decide +kernel
theorem m13_5_0_10_3 : go 13 7 9 [5, 0, 10, 3] = true := by decide +kernel
theorem m13_5_0_10_4 : go 13 7 9 [5, 0, 10, 4] = true := by decide +kernel
theorem m13_5_0_10_6 : go 13 7 9 [5, 0, 10, 6] = true := by decide +kernel
theorem m13_5_0_10_7 : go 13 7 9 [5, 0, 10, 7] = true := by decide +kernel
theorem m13_5_0_10_12 : go 13 7 9 [5, 0, 10, 12] = true := by decide +kernel

theorem m13_5_0_10 : go 13 7 10 [5, 0, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_10_1
  · exact absurd hs (by decide)
  · exact m13_5_0_10_3
  · exact m13_5_0_10_4
  · exact absurd hs (by decide)
  · exact m13_5_0_10_6
  · exact m13_5_0_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_10_12

theorem m13_5_0_11_1 : go 13 7 9 [5, 0, 11, 1] = true := by decide +kernel
theorem m13_5_0_11_3 : go 13 7 9 [5, 0, 11, 3] = true := by decide +kernel
theorem m13_5_0_11_4 : go 13 7 9 [5, 0, 11, 4] = true := by decide +kernel
theorem m13_5_0_11_6 : go 13 7 9 [5, 0, 11, 6] = true := by decide +kernel
theorem m13_5_0_11_7 : go 13 7 9 [5, 0, 11, 7] = true := by decide +kernel
theorem m13_5_0_11_9 : go 13 7 9 [5, 0, 11, 9] = true := by decide +kernel

theorem m13_5_0_11 : go 13 7 10 [5, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_11_1
  · exact absurd hs (by decide)
  · exact m13_5_0_11_3
  · exact m13_5_0_11_4
  · exact absurd hs (by decide)
  · exact m13_5_0_11_6
  · exact m13_5_0_11_7
  · exact absurd hs (by decide)
  · exact m13_5_0_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_0_12_1 : go 13 7 9 [5, 0, 12, 1] = true := by decide +kernel
theorem m13_5_0_12_3 : go 13 7 9 [5, 0, 12, 3] = true := by decide +kernel
theorem m13_5_0_12_4 : go 13 7 9 [5, 0, 12, 4] = true := by decide +kernel
theorem m13_5_0_12_6 : go 13 7 9 [5, 0, 12, 6] = true := by decide +kernel
theorem m13_5_0_12_7 : go 13 7 9 [5, 0, 12, 7] = true := by decide +kernel
theorem m13_5_0_12_9 : go 13 7 9 [5, 0, 12, 9] = true := by decide +kernel
theorem m13_5_0_12_10 : go 13 7 9 [5, 0, 12, 10] = true := by decide +kernel

theorem m13_5_0_12 : go 13 7 10 [5, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_5_0_12_1
  · exact absurd hs (by decide)
  · exact m13_5_0_12_3
  · exact m13_5_0_12_4
  · exact absurd hs (by decide)
  · exact m13_5_0_12_6
  · exact m13_5_0_12_7
  · exact absurd hs (by decide)
  · exact m13_5_0_12_9
  · exact m13_5_0_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_5_0 : go 13 7 11 [5, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_0_2
  · exact absurd hs (by decide)
  · exact m13_5_0_4
  · exact absurd hs (by decide)
  · exact m13_5_0_6
  · exact absurd hs (by decide)
  · exact m13_5_0_8
  · exact m13_5_0_9
  · exact m13_5_0_10
  · exact m13_5_0_11
  · exact m13_5_0_12

end Misses
