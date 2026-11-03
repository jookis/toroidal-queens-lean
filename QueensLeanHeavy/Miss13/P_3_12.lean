import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 12]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_12_0_2 : go 13 7 9 [3, 12, 0, 2] = true := by decide +kernel
theorem m13_3_12_0_4 : go 13 7 9 [3, 12, 0, 4] = true := by decide +kernel
theorem m13_3_12_0_5 : go 13 7 9 [3, 12, 0, 5] = true := by decide +kernel
theorem m13_3_12_0_7 : go 13 7 9 [3, 12, 0, 7] = true := by decide +kernel
theorem m13_3_12_0_8 : go 13 7 9 [3, 12, 0, 8] = true := by decide +kernel
theorem m13_3_12_0_9 : go 13 7 9 [3, 12, 0, 9] = true := by decide +kernel
theorem m13_3_12_0_11 : go 13 7 9 [3, 12, 0, 11] = true := by decide +kernel

theorem m13_3_12_0 : go 13 7 10 [3, 12, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_0_2
  · exact absurd hs (by decide)
  · exact m13_3_12_0_4
  · exact m13_3_12_0_5
  · exact absurd hs (by decide)
  · exact m13_3_12_0_7
  · exact m13_3_12_0_8
  · exact m13_3_12_0_9
  · exact absurd hs (by decide)
  · exact m13_3_12_0_11
  · exact absurd hs (by decide)

theorem m13_3_12_2_4 : go 13 7 9 [3, 12, 2, 4] = true := by decide +kernel
theorem m13_3_12_2_5 : go 13 7 9 [3, 12, 2, 5] = true := by decide +kernel
theorem m13_3_12_2_7 : go 13 7 9 [3, 12, 2, 7] = true := by decide +kernel
theorem m13_3_12_2_8 : go 13 7 9 [3, 12, 2, 8] = true := by decide +kernel
theorem m13_3_12_2_9 : go 13 7 9 [3, 12, 2, 9] = true := by decide +kernel
theorem m13_3_12_2_11 : go 13 7 9 [3, 12, 2, 11] = true := by decide +kernel

theorem m13_3_12_2 : go 13 7 10 [3, 12, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_2_4
  · exact m13_3_12_2_5
  · exact absurd hs (by decide)
  · exact m13_3_12_2_7
  · exact m13_3_12_2_8
  · exact m13_3_12_2_9
  · exact absurd hs (by decide)
  · exact m13_3_12_2_11
  · exact absurd hs (by decide)

theorem m13_3_12_4_1 : go 13 7 9 [3, 12, 4, 1] = true := by decide +kernel
theorem m13_3_12_4_2 : go 13 7 9 [3, 12, 4, 2] = true := by decide +kernel
theorem m13_3_12_4_7 : go 13 7 9 [3, 12, 4, 7] = true := by decide +kernel
theorem m13_3_12_4_8 : go 13 7 9 [3, 12, 4, 8] = true := by decide +kernel
theorem m13_3_12_4_9 : go 13 7 9 [3, 12, 4, 9] = true := by decide +kernel
theorem m13_3_12_4_11 : go 13 7 9 [3, 12, 4, 11] = true := by decide +kernel

theorem m13_3_12_4 : go 13 7 10 [3, 12, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_12_4_1
  · exact m13_3_12_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_4_7
  · exact m13_3_12_4_8
  · exact m13_3_12_4_9
  · exact absurd hs (by decide)
  · exact m13_3_12_4_11
  · exact absurd hs (by decide)

theorem m13_3_12_6_1 : go 13 7 9 [3, 12, 6, 1] = true := by decide +kernel
theorem m13_3_12_6_2 : go 13 7 9 [3, 12, 6, 2] = true := by decide +kernel
theorem m13_3_12_6_4 : go 13 7 9 [3, 12, 6, 4] = true := by decide +kernel
theorem m13_3_12_6_8 : go 13 7 9 [3, 12, 6, 8] = true := by decide +kernel
theorem m13_3_12_6_9 : go 13 7 9 [3, 12, 6, 9] = true := by decide +kernel
theorem m13_3_12_6_11 : go 13 7 9 [3, 12, 6, 11] = true := by decide +kernel

theorem m13_3_12_6 : go 13 7 10 [3, 12, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_12_6_1
  · exact m13_3_12_6_2
  · exact absurd hs (by decide)
  · exact m13_3_12_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_6_8
  · exact m13_3_12_6_9
  · exact absurd hs (by decide)
  · exact m13_3_12_6_11
  · exact absurd hs (by decide)

theorem m13_3_12_7_1 : go 13 7 9 [3, 12, 7, 1] = true := by decide +kernel
theorem m13_3_12_7_2 : go 13 7 9 [3, 12, 7, 2] = true := by decide +kernel
theorem m13_3_12_7_4 : go 13 7 9 [3, 12, 7, 4] = true := by decide +kernel
theorem m13_3_12_7_5 : go 13 7 9 [3, 12, 7, 5] = true := by decide +kernel
theorem m13_3_12_7_9 : go 13 7 9 [3, 12, 7, 9] = true := by decide +kernel
theorem m13_3_12_7_11 : go 13 7 9 [3, 12, 7, 11] = true := by decide +kernel

theorem m13_3_12_7 : go 13 7 10 [3, 12, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_12_7_1
  · exact m13_3_12_7_2
  · exact absurd hs (by decide)
  · exact m13_3_12_7_4
  · exact m13_3_12_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_7_9
  · exact absurd hs (by decide)
  · exact m13_3_12_7_11
  · exact absurd hs (by decide)

theorem m13_3_12_8_1 : go 13 7 9 [3, 12, 8, 1] = true := by decide +kernel
theorem m13_3_12_8_2 : go 13 7 9 [3, 12, 8, 2] = true := by decide +kernel
theorem m13_3_12_8_4 : go 13 7 9 [3, 12, 8, 4] = true := by decide +kernel
theorem m13_3_12_8_5 : go 13 7 9 [3, 12, 8, 5] = true := by decide +kernel
theorem m13_3_12_8_11 : go 13 7 9 [3, 12, 8, 11] = true := by decide +kernel

theorem m13_3_12_8 : go 13 7 10 [3, 12, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_12_8_1
  · exact m13_3_12_8_2
  · exact absurd hs (by decide)
  · exact m13_3_12_8_4
  · exact m13_3_12_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_8_11
  · exact absurd hs (by decide)

theorem m13_3_12_9_1 : go 13 7 9 [3, 12, 9, 1] = true := by decide +kernel
theorem m13_3_12_9_2 : go 13 7 9 [3, 12, 9, 2] = true := by decide +kernel
theorem m13_3_12_9_4 : go 13 7 9 [3, 12, 9, 4] = true := by decide +kernel
theorem m13_3_12_9_5 : go 13 7 9 [3, 12, 9, 5] = true := by decide +kernel
theorem m13_3_12_9_7 : go 13 7 9 [3, 12, 9, 7] = true := by decide +kernel
theorem m13_3_12_9_11 : go 13 7 9 [3, 12, 9, 11] = true := by decide +kernel

theorem m13_3_12_9 : go 13 7 10 [3, 12, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_12_9_1
  · exact m13_3_12_9_2
  · exact absurd hs (by decide)
  · exact m13_3_12_9_4
  · exact m13_3_12_9_5
  · exact absurd hs (by decide)
  · exact m13_3_12_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_12_9_11
  · exact absurd hs (by decide)

theorem m13_3_12_10_1 : go 13 7 9 [3, 12, 10, 1] = true := by decide +kernel
theorem m13_3_12_10_2 : go 13 7 9 [3, 12, 10, 2] = true := by decide +kernel
theorem m13_3_12_10_4 : go 13 7 9 [3, 12, 10, 4] = true := by decide +kernel
theorem m13_3_12_10_5 : go 13 7 9 [3, 12, 10, 5] = true := by decide +kernel
theorem m13_3_12_10_7 : go 13 7 9 [3, 12, 10, 7] = true := by decide +kernel
theorem m13_3_12_10_8 : go 13 7 9 [3, 12, 10, 8] = true := by decide +kernel

theorem m13_3_12_10 : go 13 7 10 [3, 12, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_12_10_1
  · exact m13_3_12_10_2
  · exact absurd hs (by decide)
  · exact m13_3_12_10_4
  · exact m13_3_12_10_5
  · exact absurd hs (by decide)
  · exact m13_3_12_10_7
  · exact m13_3_12_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_12 : go 13 7 11 [3, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_3_12_0
  · exact absurd hs (by decide)
  · exact m13_3_12_2
  · exact absurd hs (by decide)
  · exact m13_3_12_4
  · exact absurd hs (by decide)
  · exact m13_3_12_6
  · exact m13_3_12_7
  · exact m13_3_12_8
  · exact m13_3_12_9
  · exact m13_3_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
