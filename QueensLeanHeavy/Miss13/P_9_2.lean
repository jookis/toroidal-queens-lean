import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [9, 2]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_9_2_0_3 : go 13 7 9 [9, 2, 0, 3] = true := by decide +kernel
theorem m13_9_2_0_5 : go 13 7 9 [9, 2, 0, 5] = true := by decide +kernel
theorem m13_9_2_0_7 : go 13 7 9 [9, 2, 0, 7] = true := by decide +kernel
theorem m13_9_2_0_8 : go 13 7 9 [9, 2, 0, 8] = true := by decide +kernel
theorem m13_9_2_0_10 : go 13 7 9 [9, 2, 0, 10] = true := by decide +kernel
theorem m13_9_2_0_11 : go 13 7 9 [9, 2, 0, 11] = true := by decide +kernel

theorem m13_9_2_0 : go 13 7 10 [9, 2, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_2_0_3
  · exact absurd hs (by decide)
  · exact m13_9_2_0_5
  · exact absurd hs (by decide)
  · exact m13_9_2_0_7
  · exact m13_9_2_0_8
  · exact absurd hs (by decide)
  · exact m13_9_2_0_10
  · exact m13_9_2_0_11
  · exact absurd hs (by decide)

theorem m13_9_2_4_1 : go 13 7 9 [9, 2, 4, 1] = true := by decide +kernel
theorem m13_9_2_4_7 : go 13 7 9 [9, 2, 4, 7] = true := by decide +kernel
theorem m13_9_2_4_8 : go 13 7 9 [9, 2, 4, 8] = true := by decide +kernel
theorem m13_9_2_4_10 : go 13 7 9 [9, 2, 4, 10] = true := by decide +kernel
theorem m13_9_2_4_11 : go 13 7 9 [9, 2, 4, 11] = true := by decide +kernel

theorem m13_9_2_4 : go 13 7 10 [9, 2, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_9_2_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_2_4_7
  · exact m13_9_2_4_8
  · exact absurd hs (by decide)
  · exact m13_9_2_4_10
  · exact m13_9_2_4_11
  · exact absurd hs (by decide)

theorem m13_9_2_5_1 : go 13 7 9 [9, 2, 5, 1] = true := by decide +kernel
theorem m13_9_2_5_3 : go 13 7 9 [9, 2, 5, 3] = true := by decide +kernel
theorem m13_9_2_5_7 : go 13 7 9 [9, 2, 5, 7] = true := by decide +kernel
theorem m13_9_2_5_8 : go 13 7 9 [9, 2, 5, 8] = true := by decide +kernel
theorem m13_9_2_5_10 : go 13 7 9 [9, 2, 5, 10] = true := by decide +kernel
theorem m13_9_2_5_11 : go 13 7 9 [9, 2, 5, 11] = true := by decide +kernel

theorem m13_9_2_5 : go 13 7 10 [9, 2, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_9_2_5_1
  · exact absurd hs (by decide)
  · exact m13_9_2_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_2_5_7
  · exact m13_9_2_5_8
  · exact absurd hs (by decide)
  · exact m13_9_2_5_10
  · exact m13_9_2_5_11
  · exact absurd hs (by decide)

theorem m13_9_2_6_1 : go 13 7 9 [9, 2, 6, 1] = true := by decide +kernel
theorem m13_9_2_6_3 : go 13 7 9 [9, 2, 6, 3] = true := by decide +kernel
theorem m13_9_2_6_8 : go 13 7 9 [9, 2, 6, 8] = true := by decide +kernel
theorem m13_9_2_6_10 : go 13 7 9 [9, 2, 6, 10] = true := by decide +kernel
theorem m13_9_2_6_11 : go 13 7 9 [9, 2, 6, 11] = true := by decide +kernel

theorem m13_9_2_6 : go 13 7 10 [9, 2, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_9_2_6_1
  · exact absurd hs (by decide)
  · exact m13_9_2_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_2_6_8
  · exact absurd hs (by decide)
  · exact m13_9_2_6_10
  · exact m13_9_2_6_11
  · exact absurd hs (by decide)

theorem m13_9_2_8_1 : go 13 7 9 [9, 2, 8, 1] = true := by decide +kernel
theorem m13_9_2_8_3 : go 13 7 9 [9, 2, 8, 3] = true := by decide +kernel
theorem m13_9_2_8_5 : go 13 7 9 [9, 2, 8, 5] = true := by decide +kernel
theorem m13_9_2_8_10 : go 13 7 9 [9, 2, 8, 10] = true := by decide +kernel
theorem m13_9_2_8_11 : go 13 7 9 [9, 2, 8, 11] = true := by decide +kernel

theorem m13_9_2_8 : go 13 7 10 [9, 2, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_9_2_8_1
  · exact absurd hs (by decide)
  · exact m13_9_2_8_3
  · exact absurd hs (by decide)
  · exact m13_9_2_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_2_8_10
  · exact m13_9_2_8_11
  · exact absurd hs (by decide)

theorem m13_9_2_10_1 : go 13 7 9 [9, 2, 10, 1] = true := by decide +kernel
theorem m13_9_2_10_3 : go 13 7 9 [9, 2, 10, 3] = true := by decide +kernel
theorem m13_9_2_10_5 : go 13 7 9 [9, 2, 10, 5] = true := by decide +kernel
theorem m13_9_2_10_7 : go 13 7 9 [9, 2, 10, 7] = true := by decide +kernel
theorem m13_9_2_10_8 : go 13 7 9 [9, 2, 10, 8] = true := by decide +kernel

theorem m13_9_2_10 : go 13 7 10 [9, 2, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_9_2_10_1
  · exact absurd hs (by decide)
  · exact m13_9_2_10_3
  · exact absurd hs (by decide)
  · exact m13_9_2_10_5
  · exact absurd hs (by decide)
  · exact m13_9_2_10_7
  · exact m13_9_2_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_2_12_1 : go 13 7 9 [9, 2, 12, 1] = true := by decide +kernel
theorem m13_9_2_12_3 : go 13 7 9 [9, 2, 12, 3] = true := by decide +kernel
theorem m13_9_2_12_5 : go 13 7 9 [9, 2, 12, 5] = true := by decide +kernel
theorem m13_9_2_12_7 : go 13 7 9 [9, 2, 12, 7] = true := by decide +kernel
theorem m13_9_2_12_8 : go 13 7 9 [9, 2, 12, 8] = true := by decide +kernel
theorem m13_9_2_12_10 : go 13 7 9 [9, 2, 12, 10] = true := by decide +kernel

theorem m13_9_2_12 : go 13 7 10 [9, 2, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_9_2_12_1
  · exact absurd hs (by decide)
  · exact m13_9_2_12_3
  · exact absurd hs (by decide)
  · exact m13_9_2_12_5
  · exact absurd hs (by decide)
  · exact m13_9_2_12_7
  · exact m13_9_2_12_8
  · exact absurd hs (by decide)
  · exact m13_9_2_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_2 : go 13 7 11 [9, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_2_4
  · exact m13_9_2_5
  · exact m13_9_2_6
  · exact absurd hs (by decide)
  · exact m13_9_2_8
  · exact absurd hs (by decide)
  · exact m13_9_2_10
  · exact absurd hs (by decide)
  · exact m13_9_2_12

end Misses
