import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [8, 1]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_8_1_3_0 : go 13 7 9 [8, 1, 3, 0] = true := by decide +kernel
theorem m13_8_1_3_6 : go 13 7 9 [8, 1, 3, 6] = true := by decide +kernel
theorem m13_8_1_3_7 : go 13 7 9 [8, 1, 3, 7] = true := by decide +kernel
theorem m13_8_1_3_9 : go 13 7 9 [8, 1, 3, 9] = true := by decide +kernel
theorem m13_8_1_3_10 : go 13 7 9 [8, 1, 3, 10] = true := by decide +kernel
theorem m13_8_1_3_12 : go 13 7 9 [8, 1, 3, 12] = true := by decide +kernel

theorem m13_8_1_3 : go 13 7 10 [8, 1, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_1_3_6
  · exact m13_8_1_3_7
  · exact absurd hs (by decide)
  · exact m13_8_1_3_9
  · exact m13_8_1_3_10
  · exact absurd hs (by decide)
  · exact m13_8_1_3_12

theorem m13_8_1_4_0 : go 13 7 9 [8, 1, 4, 0] = true := by decide +kernel
theorem m13_8_1_4_2 : go 13 7 9 [8, 1, 4, 2] = true := by decide +kernel
theorem m13_8_1_4_6 : go 13 7 9 [8, 1, 4, 6] = true := by decide +kernel
theorem m13_8_1_4_7 : go 13 7 9 [8, 1, 4, 7] = true := by decide +kernel
theorem m13_8_1_4_9 : go 13 7 9 [8, 1, 4, 9] = true := by decide +kernel
theorem m13_8_1_4_10 : go 13 7 9 [8, 1, 4, 10] = true := by decide +kernel
theorem m13_8_1_4_12 : go 13 7 9 [8, 1, 4, 12] = true := by decide +kernel

theorem m13_8_1_4 : go 13 7 10 [8, 1, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_4_0
  · exact absurd hs (by decide)
  · exact m13_8_1_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_1_4_6
  · exact m13_8_1_4_7
  · exact absurd hs (by decide)
  · exact m13_8_1_4_9
  · exact m13_8_1_4_10
  · exact absurd hs (by decide)
  · exact m13_8_1_4_12

theorem m13_8_1_5_0 : go 13 7 9 [8, 1, 5, 0] = true := by decide +kernel
theorem m13_8_1_5_2 : go 13 7 9 [8, 1, 5, 2] = true := by decide +kernel
theorem m13_8_1_5_7 : go 13 7 9 [8, 1, 5, 7] = true := by decide +kernel
theorem m13_8_1_5_9 : go 13 7 9 [8, 1, 5, 9] = true := by decide +kernel
theorem m13_8_1_5_10 : go 13 7 9 [8, 1, 5, 10] = true := by decide +kernel
theorem m13_8_1_5_12 : go 13 7 9 [8, 1, 5, 12] = true := by decide +kernel

theorem m13_8_1_5 : go 13 7 10 [8, 1, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_5_0
  · exact absurd hs (by decide)
  · exact m13_8_1_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_1_5_7
  · exact absurd hs (by decide)
  · exact m13_8_1_5_9
  · exact m13_8_1_5_10
  · exact absurd hs (by decide)
  · exact m13_8_1_5_12

theorem m13_8_1_7_0 : go 13 7 9 [8, 1, 7, 0] = true := by decide +kernel
theorem m13_8_1_7_2 : go 13 7 9 [8, 1, 7, 2] = true := by decide +kernel
theorem m13_8_1_7_4 : go 13 7 9 [8, 1, 7, 4] = true := by decide +kernel
theorem m13_8_1_7_9 : go 13 7 9 [8, 1, 7, 9] = true := by decide +kernel
theorem m13_8_1_7_10 : go 13 7 9 [8, 1, 7, 10] = true := by decide +kernel
theorem m13_8_1_7_12 : go 13 7 9 [8, 1, 7, 12] = true := by decide +kernel

theorem m13_8_1_7 : go 13 7 10 [8, 1, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_7_0
  · exact absurd hs (by decide)
  · exact m13_8_1_7_2
  · exact absurd hs (by decide)
  · exact m13_8_1_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_1_7_9
  · exact m13_8_1_7_10
  · exact absurd hs (by decide)
  · exact m13_8_1_7_12

theorem m13_8_1_9_0 : go 13 7 9 [8, 1, 9, 0] = true := by decide +kernel
theorem m13_8_1_9_2 : go 13 7 9 [8, 1, 9, 2] = true := by decide +kernel
theorem m13_8_1_9_4 : go 13 7 9 [8, 1, 9, 4] = true := by decide +kernel
theorem m13_8_1_9_6 : go 13 7 9 [8, 1, 9, 6] = true := by decide +kernel
theorem m13_8_1_9_7 : go 13 7 9 [8, 1, 9, 7] = true := by decide +kernel
theorem m13_8_1_9_12 : go 13 7 9 [8, 1, 9, 12] = true := by decide +kernel

theorem m13_8_1_9 : go 13 7 10 [8, 1, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_9_0
  · exact absurd hs (by decide)
  · exact m13_8_1_9_2
  · exact absurd hs (by decide)
  · exact m13_8_1_9_4
  · exact absurd hs (by decide)
  · exact m13_8_1_9_6
  · exact m13_8_1_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_1_9_12

theorem m13_8_1_11_0 : go 13 7 9 [8, 1, 11, 0] = true := by decide +kernel
theorem m13_8_1_11_2 : go 13 7 9 [8, 1, 11, 2] = true := by decide +kernel
theorem m13_8_1_11_4 : go 13 7 9 [8, 1, 11, 4] = true := by decide +kernel
theorem m13_8_1_11_6 : go 13 7 9 [8, 1, 11, 6] = true := by decide +kernel
theorem m13_8_1_11_7 : go 13 7 9 [8, 1, 11, 7] = true := by decide +kernel
theorem m13_8_1_11_9 : go 13 7 9 [8, 1, 11, 9] = true := by decide +kernel

theorem m13_8_1_11 : go 13 7 10 [8, 1, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_11_0
  · exact absurd hs (by decide)
  · exact m13_8_1_11_2
  · exact absurd hs (by decide)
  · exact m13_8_1_11_4
  · exact absurd hs (by decide)
  · exact m13_8_1_11_6
  · exact m13_8_1_11_7
  · exact absurd hs (by decide)
  · exact m13_8_1_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_1_12_0 : go 13 7 9 [8, 1, 12, 0] = true := by decide +kernel
theorem m13_8_1_12_2 : go 13 7 9 [8, 1, 12, 2] = true := by decide +kernel
theorem m13_8_1_12_4 : go 13 7 9 [8, 1, 12, 4] = true := by decide +kernel
theorem m13_8_1_12_6 : go 13 7 9 [8, 1, 12, 6] = true := by decide +kernel
theorem m13_8_1_12_7 : go 13 7 9 [8, 1, 12, 7] = true := by decide +kernel
theorem m13_8_1_12_9 : go 13 7 9 [8, 1, 12, 9] = true := by decide +kernel
theorem m13_8_1_12_10 : go 13 7 9 [8, 1, 12, 10] = true := by decide +kernel

theorem m13_8_1_12 : go 13 7 10 [8, 1, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_1_12_0
  · exact absurd hs (by decide)
  · exact m13_8_1_12_2
  · exact absurd hs (by decide)
  · exact m13_8_1_12_4
  · exact absurd hs (by decide)
  · exact m13_8_1_12_6
  · exact m13_8_1_12_7
  · exact absurd hs (by decide)
  · exact m13_8_1_12_9
  · exact m13_8_1_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_1 : go 13 7 11 [8, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_1_3
  · exact m13_8_1_4
  · exact m13_8_1_5
  · exact absurd hs (by decide)
  · exact m13_8_1_7
  · exact absurd hs (by decide)
  · exact m13_8_1_9
  · exact absurd hs (by decide)
  · exact m13_8_1_11
  · exact m13_8_1_12

end Misses
