import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [3, 8]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_3_8_0_2 : go 13 7 9 [3, 8, 0, 2] = true := by decide +kernel
theorem m13_3_8_0_4 : go 13 7 9 [3, 8, 0, 4] = true := by decide +kernel
theorem m13_3_8_0_5 : go 13 7 9 [3, 8, 0, 5] = true := by decide +kernel
theorem m13_3_8_0_7 : go 13 7 9 [3, 8, 0, 7] = true := by decide +kernel
theorem m13_3_8_0_9 : go 13 7 9 [3, 8, 0, 9] = true := by decide +kernel
theorem m13_3_8_0_11 : go 13 7 9 [3, 8, 0, 11] = true := by decide +kernel
theorem m13_3_8_0_12 : go 13 7 9 [3, 8, 0, 12] = true := by decide +kernel

theorem m13_3_8_0 : go 13 7 10 [3, 8, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_8_0_2
  · exact absurd hs (by decide)
  · exact m13_3_8_0_4
  · exact m13_3_8_0_5
  · exact absurd hs (by decide)
  · exact m13_3_8_0_7
  · exact absurd hs (by decide)
  · exact m13_3_8_0_9
  · exact absurd hs (by decide)
  · exact m13_3_8_0_11
  · exact m13_3_8_0_12

theorem m13_3_8_2_4 : go 13 7 9 [3, 8, 2, 4] = true := by decide +kernel
theorem m13_3_8_2_5 : go 13 7 9 [3, 8, 2, 5] = true := by decide +kernel
theorem m13_3_8_2_7 : go 13 7 9 [3, 8, 2, 7] = true := by decide +kernel
theorem m13_3_8_2_9 : go 13 7 9 [3, 8, 2, 9] = true := by decide +kernel
theorem m13_3_8_2_11 : go 13 7 9 [3, 8, 2, 11] = true := by decide +kernel
theorem m13_3_8_2_12 : go 13 7 9 [3, 8, 2, 12] = true := by decide +kernel

theorem m13_3_8_2 : go 13 7 10 [3, 8, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_8_2_4
  · exact m13_3_8_2_5
  · exact absurd hs (by decide)
  · exact m13_3_8_2_7
  · exact absurd hs (by decide)
  · exact m13_3_8_2_9
  · exact absurd hs (by decide)
  · exact m13_3_8_2_11
  · exact m13_3_8_2_12

theorem m13_3_8_4_1 : go 13 7 9 [3, 8, 4, 1] = true := by decide +kernel
theorem m13_3_8_4_2 : go 13 7 9 [3, 8, 4, 2] = true := by decide +kernel
theorem m13_3_8_4_7 : go 13 7 9 [3, 8, 4, 7] = true := by decide +kernel
theorem m13_3_8_4_9 : go 13 7 9 [3, 8, 4, 9] = true := by decide +kernel
theorem m13_3_8_4_11 : go 13 7 9 [3, 8, 4, 11] = true := by decide +kernel
theorem m13_3_8_4_12 : go 13 7 9 [3, 8, 4, 12] = true := by decide +kernel

theorem m13_3_8_4 : go 13 7 10 [3, 8, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_8_4_1
  · exact m13_3_8_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_8_4_7
  · exact absurd hs (by decide)
  · exact m13_3_8_4_9
  · exact absurd hs (by decide)
  · exact m13_3_8_4_11
  · exact m13_3_8_4_12

theorem m13_3_8_6_1 : go 13 7 9 [3, 8, 6, 1] = true := by decide +kernel
theorem m13_3_8_6_2 : go 13 7 9 [3, 8, 6, 2] = true := by decide +kernel
theorem m13_3_8_6_4 : go 13 7 9 [3, 8, 6, 4] = true := by decide +kernel
theorem m13_3_8_6_9 : go 13 7 9 [3, 8, 6, 9] = true := by decide +kernel
theorem m13_3_8_6_11 : go 13 7 9 [3, 8, 6, 11] = true := by decide +kernel
theorem m13_3_8_6_12 : go 13 7 9 [3, 8, 6, 12] = true := by decide +kernel

theorem m13_3_8_6 : go 13 7 10 [3, 8, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_8_6_1
  · exact m13_3_8_6_2
  · exact absurd hs (by decide)
  · exact m13_3_8_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_8_6_9
  · exact absurd hs (by decide)
  · exact m13_3_8_6_11
  · exact m13_3_8_6_12

theorem m13_3_8_10_1 : go 13 7 9 [3, 8, 10, 1] = true := by decide +kernel
theorem m13_3_8_10_2 : go 13 7 9 [3, 8, 10, 2] = true := by decide +kernel
theorem m13_3_8_10_4 : go 13 7 9 [3, 8, 10, 4] = true := by decide +kernel
theorem m13_3_8_10_5 : go 13 7 9 [3, 8, 10, 5] = true := by decide +kernel
theorem m13_3_8_10_7 : go 13 7 9 [3, 8, 10, 7] = true := by decide +kernel
theorem m13_3_8_10_12 : go 13 7 9 [3, 8, 10, 12] = true := by decide +kernel

theorem m13_3_8_10 : go 13 7 10 [3, 8, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_8_10_1
  · exact m13_3_8_10_2
  · exact absurd hs (by decide)
  · exact m13_3_8_10_4
  · exact m13_3_8_10_5
  · exact absurd hs (by decide)
  · exact m13_3_8_10_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_8_10_12

theorem m13_3_8_11_1 : go 13 7 9 [3, 8, 11, 1] = true := by decide +kernel
theorem m13_3_8_11_2 : go 13 7 9 [3, 8, 11, 2] = true := by decide +kernel
theorem m13_3_8_11_4 : go 13 7 9 [3, 8, 11, 4] = true := by decide +kernel
theorem m13_3_8_11_5 : go 13 7 9 [3, 8, 11, 5] = true := by decide +kernel
theorem m13_3_8_11_7 : go 13 7 9 [3, 8, 11, 7] = true := by decide +kernel
theorem m13_3_8_11_9 : go 13 7 9 [3, 8, 11, 9] = true := by decide +kernel

theorem m13_3_8_11 : go 13 7 10 [3, 8, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_8_11_1
  · exact m13_3_8_11_2
  · exact absurd hs (by decide)
  · exact m13_3_8_11_4
  · exact m13_3_8_11_5
  · exact absurd hs (by decide)
  · exact m13_3_8_11_7
  · exact absurd hs (by decide)
  · exact m13_3_8_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_8_12_1 : go 13 7 9 [3, 8, 12, 1] = true := by decide +kernel
theorem m13_3_8_12_2 : go 13 7 9 [3, 8, 12, 2] = true := by decide +kernel
theorem m13_3_8_12_4 : go 13 7 9 [3, 8, 12, 4] = true := by decide +kernel
theorem m13_3_8_12_5 : go 13 7 9 [3, 8, 12, 5] = true := by decide +kernel
theorem m13_3_8_12_7 : go 13 7 9 [3, 8, 12, 7] = true := by decide +kernel
theorem m13_3_8_12_9 : go 13 7 9 [3, 8, 12, 9] = true := by decide +kernel

theorem m13_3_8_12 : go 13 7 10 [3, 8, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_3_8_12_1
  · exact m13_3_8_12_2
  · exact absurd hs (by decide)
  · exact m13_3_8_12_4
  · exact m13_3_8_12_5
  · exact absurd hs (by decide)
  · exact m13_3_8_12_7
  · exact absurd hs (by decide)
  · exact m13_3_8_12_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_3_8 : go 13 7 11 [3, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_3_8_0
  · exact absurd hs (by decide)
  · exact m13_3_8_2
  · exact absurd hs (by decide)
  · exact m13_3_8_4
  · exact absurd hs (by decide)
  · exact m13_3_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_3_8_10
  · exact m13_3_8_11
  · exact m13_3_8_12

end Misses
