import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 10]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_10_0_2 : go 13 7 9 [3, 10, 0, 2] = true := by decide +kernel
theorem m13_3_10_0_4 : go 13 7 9 [3, 10, 0, 4] = true := by decide +kernel
theorem m13_3_10_0_5 : go 13 7 9 [3, 10, 0, 5] = true := by decide +kernel
theorem m13_3_10_0_7 : go 13 7 9 [3, 10, 0, 7] = true := by decide +kernel
theorem m13_3_10_0_9 : go 13 7 9 [3, 10, 0, 9] = true := by decide +kernel
theorem m13_3_10_0_11 : go 13 7 9 [3, 10, 0, 11] = true := by decide +kernel

theorem m13_3_10_0 : go 13 7 10 [3, 10, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_0_2
  · exact absurd hs (by decide)
  · exact m13_3_10_0_4
  · exact m13_3_10_0_5
  · exact absurd hs (by decide)
  · exact m13_3_10_0_7
  · exact absurd hs (by decide)
  · exact m13_3_10_0_9
  · exact absurd hs (by decide)
  · exact m13_3_10_0_11
  · exact absurd hs (by decide)

theorem m13_3_10_2_4 : go 13 7 9 [3, 10, 2, 4] = true := by decide +kernel
theorem m13_3_10_2_5 : go 13 7 9 [3, 10, 2, 5] = true := by decide +kernel
theorem m13_3_10_2_7 : go 13 7 9 [3, 10, 2, 7] = true := by decide +kernel
theorem m13_3_10_2_9 : go 13 7 9 [3, 10, 2, 9] = true := by decide +kernel
theorem m13_3_10_2_11 : go 13 7 9 [3, 10, 2, 11] = true := by decide +kernel

theorem m13_3_10_2 : go 13 7 10 [3, 10, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_2_4
  · exact m13_3_10_2_5
  · exact absurd hs (by decide)
  · exact m13_3_10_2_7
  · exact absurd hs (by decide)
  · exact m13_3_10_2_9
  · exact absurd hs (by decide)
  · exact m13_3_10_2_11
  · exact absurd hs (by decide)

theorem m13_3_10_4_1 : go 13 7 9 [3, 10, 4, 1] = true := by decide +kernel
theorem m13_3_10_4_2 : go 13 7 9 [3, 10, 4, 2] = true := by decide +kernel
theorem m13_3_10_4_7 : go 13 7 9 [3, 10, 4, 7] = true := by decide +kernel
theorem m13_3_10_4_9 : go 13 7 9 [3, 10, 4, 9] = true := by decide +kernel
theorem m13_3_10_4_11 : go 13 7 9 [3, 10, 4, 11] = true := by decide +kernel

theorem m13_3_10_4 : go 13 7 10 [3, 10, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_10_4_1
  · exact m13_3_10_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_4_7
  · exact absurd hs (by decide)
  · exact m13_3_10_4_9
  · exact absurd hs (by decide)
  · exact m13_3_10_4_11
  · exact absurd hs (by decide)

theorem m13_3_10_6_1 : go 13 7 9 [3, 10, 6, 1] = true := by decide +kernel
theorem m13_3_10_6_2 : go 13 7 9 [3, 10, 6, 2] = true := by decide +kernel
theorem m13_3_10_6_4 : go 13 7 9 [3, 10, 6, 4] = true := by decide +kernel
theorem m13_3_10_6_9 : go 13 7 9 [3, 10, 6, 9] = true := by decide +kernel
theorem m13_3_10_6_11 : go 13 7 9 [3, 10, 6, 11] = true := by decide +kernel

theorem m13_3_10_6 : go 13 7 10 [3, 10, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_10_6_1
  · exact m13_3_10_6_2
  · exact absurd hs (by decide)
  · exact m13_3_10_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_6_9
  · exact absurd hs (by decide)
  · exact m13_3_10_6_11
  · exact absurd hs (by decide)

theorem m13_3_10_7_1 : go 13 7 9 [3, 10, 7, 1] = true := by decide +kernel
theorem m13_3_10_7_2 : go 13 7 9 [3, 10, 7, 2] = true := by decide +kernel
theorem m13_3_10_7_4 : go 13 7 9 [3, 10, 7, 4] = true := by decide +kernel
theorem m13_3_10_7_5 : go 13 7 9 [3, 10, 7, 5] = true := by decide +kernel
theorem m13_3_10_7_9 : go 13 7 9 [3, 10, 7, 9] = true := by decide +kernel
theorem m13_3_10_7_11 : go 13 7 9 [3, 10, 7, 11] = true := by decide +kernel

theorem m13_3_10_7 : go 13 7 10 [3, 10, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_10_7_1
  · exact m13_3_10_7_2
  · exact absurd hs (by decide)
  · exact m13_3_10_7_4
  · exact m13_3_10_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_7_9
  · exact absurd hs (by decide)
  · exact m13_3_10_7_11
  · exact absurd hs (by decide)

theorem m13_3_10_8_1 : go 13 7 9 [3, 10, 8, 1] = true := by decide +kernel
theorem m13_3_10_8_2 : go 13 7 9 [3, 10, 8, 2] = true := by decide +kernel
theorem m13_3_10_8_4 : go 13 7 9 [3, 10, 8, 4] = true := by decide +kernel
theorem m13_3_10_8_5 : go 13 7 9 [3, 10, 8, 5] = true := by decide +kernel
theorem m13_3_10_8_11 : go 13 7 9 [3, 10, 8, 11] = true := by decide +kernel

theorem m13_3_10_8 : go 13 7 10 [3, 10, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_10_8_1
  · exact m13_3_10_8_2
  · exact absurd hs (by decide)
  · exact m13_3_10_8_4
  · exact m13_3_10_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_8_11
  · exact absurd hs (by decide)

theorem m13_3_10_12_1 : go 13 7 9 [3, 10, 12, 1] = true := by decide +kernel
theorem m13_3_10_12_2 : go 13 7 9 [3, 10, 12, 2] = true := by decide +kernel
theorem m13_3_10_12_4 : go 13 7 9 [3, 10, 12, 4] = true := by decide +kernel
theorem m13_3_10_12_5 : go 13 7 9 [3, 10, 12, 5] = true := by decide +kernel
theorem m13_3_10_12_7 : go 13 7 9 [3, 10, 12, 7] = true := by decide +kernel
theorem m13_3_10_12_9 : go 13 7 9 [3, 10, 12, 9] = true := by decide +kernel

theorem m13_3_10_12 : go 13 7 10 [3, 10, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_10_12_1
  · exact m13_3_10_12_2
  · exact absurd hs (by decide)
  · exact m13_3_10_12_4
  · exact m13_3_10_12_5
  · exact absurd hs (by decide)
  · exact m13_3_10_12_7
  · exact absurd hs (by decide)
  · exact m13_3_10_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_10 : go 13 7 11 [3, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_3_10_0
  · exact absurd hs (by decide)
  · exact m13_3_10_2
  · exact absurd hs (by decide)
  · exact m13_3_10_4
  · exact absurd hs (by decide)
  · exact m13_3_10_6
  · exact m13_3_10_7
  · exact m13_3_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_10_12

end Misses
