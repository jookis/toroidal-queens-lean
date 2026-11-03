import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [8, 3]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_8_3_0_2 : go 13 7 9 [8, 3, 0, 2] = true := by decide +kernel
theorem m13_8_3_0_4 : go 13 7 9 [8, 3, 0, 4] = true := by decide +kernel
theorem m13_8_3_0_6 : go 13 7 9 [8, 3, 0, 6] = true := by decide +kernel
theorem m13_8_3_0_7 : go 13 7 9 [8, 3, 0, 7] = true := by decide +kernel
theorem m13_8_3_0_9 : go 13 7 9 [8, 3, 0, 9] = true := by decide +kernel
theorem m13_8_3_0_10 : go 13 7 9 [8, 3, 0, 10] = true := by decide +kernel
theorem m13_8_3_0_12 : go 13 7 9 [8, 3, 0, 12] = true := by decide +kernel

theorem m13_8_3_0 : go 13 7 10 [8, 3, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_3_0_2
  · exact absurd hs (by decide)
  · exact m13_8_3_0_4
  · exact absurd hs (by decide)
  · exact m13_8_3_0_6
  · exact m13_8_3_0_7
  · exact absurd hs (by decide)
  · exact m13_8_3_0_9
  · exact m13_8_3_0_10
  · exact absurd hs (by decide)
  · exact m13_8_3_0_12

theorem m13_8_3_1_4 : go 13 7 9 [8, 3, 1, 4] = true := by decide +kernel
theorem m13_8_3_1_6 : go 13 7 9 [8, 3, 1, 6] = true := by decide +kernel
theorem m13_8_3_1_7 : go 13 7 9 [8, 3, 1, 7] = true := by decide +kernel
theorem m13_8_3_1_9 : go 13 7 9 [8, 3, 1, 9] = true := by decide +kernel
theorem m13_8_3_1_10 : go 13 7 9 [8, 3, 1, 10] = true := by decide +kernel
theorem m13_8_3_1_12 : go 13 7 9 [8, 3, 1, 12] = true := by decide +kernel

theorem m13_8_3_1 : go 13 7 10 [8, 3, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_3_1_4
  · exact absurd hs (by decide)
  · exact m13_8_3_1_6
  · exact m13_8_3_1_7
  · exact absurd hs (by decide)
  · exact m13_8_3_1_9
  · exact m13_8_3_1_10
  · exact absurd hs (by decide)
  · exact m13_8_3_1_12

theorem m13_8_3_5_0 : go 13 7 9 [8, 3, 5, 0] = true := by decide +kernel
theorem m13_8_3_5_2 : go 13 7 9 [8, 3, 5, 2] = true := by decide +kernel
theorem m13_8_3_5_7 : go 13 7 9 [8, 3, 5, 7] = true := by decide +kernel
theorem m13_8_3_5_9 : go 13 7 9 [8, 3, 5, 9] = true := by decide +kernel
theorem m13_8_3_5_10 : go 13 7 9 [8, 3, 5, 10] = true := by decide +kernel
theorem m13_8_3_5_12 : go 13 7 9 [8, 3, 5, 12] = true := by decide +kernel

theorem m13_8_3_5 : go 13 7 10 [8, 3, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_3_5_0
  · exact absurd hs (by decide)
  · exact m13_8_3_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_3_5_7
  · exact absurd hs (by decide)
  · exact m13_8_3_5_9
  · exact m13_8_3_5_10
  · exact absurd hs (by decide)
  · exact m13_8_3_5_12

theorem m13_8_3_7_0 : go 13 7 9 [8, 3, 7, 0] = true := by decide +kernel
theorem m13_8_3_7_2 : go 13 7 9 [8, 3, 7, 2] = true := by decide +kernel
theorem m13_8_3_7_4 : go 13 7 9 [8, 3, 7, 4] = true := by decide +kernel
theorem m13_8_3_7_9 : go 13 7 9 [8, 3, 7, 9] = true := by decide +kernel
theorem m13_8_3_7_10 : go 13 7 9 [8, 3, 7, 10] = true := by decide +kernel
theorem m13_8_3_7_12 : go 13 7 9 [8, 3, 7, 12] = true := by decide +kernel

theorem m13_8_3_7 : go 13 7 10 [8, 3, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_3_7_0
  · exact absurd hs (by decide)
  · exact m13_8_3_7_2
  · exact absurd hs (by decide)
  · exact m13_8_3_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_3_7_9
  · exact m13_8_3_7_10
  · exact absurd hs (by decide)
  · exact m13_8_3_7_12

theorem m13_8_3_9_0 : go 13 7 9 [8, 3, 9, 0] = true := by decide +kernel
theorem m13_8_3_9_2 : go 13 7 9 [8, 3, 9, 2] = true := by decide +kernel
theorem m13_8_3_9_4 : go 13 7 9 [8, 3, 9, 4] = true := by decide +kernel
theorem m13_8_3_9_6 : go 13 7 9 [8, 3, 9, 6] = true := by decide +kernel
theorem m13_8_3_9_7 : go 13 7 9 [8, 3, 9, 7] = true := by decide +kernel
theorem m13_8_3_9_12 : go 13 7 9 [8, 3, 9, 12] = true := by decide +kernel

theorem m13_8_3_9 : go 13 7 10 [8, 3, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_3_9_0
  · exact absurd hs (by decide)
  · exact m13_8_3_9_2
  · exact absurd hs (by decide)
  · exact m13_8_3_9_4
  · exact absurd hs (by decide)
  · exact m13_8_3_9_6
  · exact m13_8_3_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_3_9_12

theorem m13_8_3_11_0 : go 13 7 9 [8, 3, 11, 0] = true := by decide +kernel
theorem m13_8_3_11_2 : go 13 7 9 [8, 3, 11, 2] = true := by decide +kernel
theorem m13_8_3_11_4 : go 13 7 9 [8, 3, 11, 4] = true := by decide +kernel
theorem m13_8_3_11_6 : go 13 7 9 [8, 3, 11, 6] = true := by decide +kernel
theorem m13_8_3_11_7 : go 13 7 9 [8, 3, 11, 7] = true := by decide +kernel
theorem m13_8_3_11_9 : go 13 7 9 [8, 3, 11, 9] = true := by decide +kernel

theorem m13_8_3_11 : go 13 7 10 [8, 3, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_3_11_0
  · exact absurd hs (by decide)
  · exact m13_8_3_11_2
  · exact absurd hs (by decide)
  · exact m13_8_3_11_4
  · exact absurd hs (by decide)
  · exact m13_8_3_11_6
  · exact m13_8_3_11_7
  · exact absurd hs (by decide)
  · exact m13_8_3_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_3_12_0 : go 13 7 9 [8, 3, 12, 0] = true := by decide +kernel
theorem m13_8_3_12_2 : go 13 7 9 [8, 3, 12, 2] = true := by decide +kernel
theorem m13_8_3_12_4 : go 13 7 9 [8, 3, 12, 4] = true := by decide +kernel
theorem m13_8_3_12_6 : go 13 7 9 [8, 3, 12, 6] = true := by decide +kernel
theorem m13_8_3_12_7 : go 13 7 9 [8, 3, 12, 7] = true := by decide +kernel
theorem m13_8_3_12_9 : go 13 7 9 [8, 3, 12, 9] = true := by decide +kernel
theorem m13_8_3_12_10 : go 13 7 9 [8, 3, 12, 10] = true := by decide +kernel

theorem m13_8_3_12 : go 13 7 10 [8, 3, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_3_12_0
  · exact absurd hs (by decide)
  · exact m13_8_3_12_2
  · exact absurd hs (by decide)
  · exact m13_8_3_12_4
  · exact absurd hs (by decide)
  · exact m13_8_3_12_6
  · exact m13_8_3_12_7
  · exact absurd hs (by decide)
  · exact m13_8_3_12_9
  · exact m13_8_3_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_3 : go 13 7 11 [8, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_3_0
  · exact m13_8_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_3_5
  · exact absurd hs (by decide)
  · exact m13_8_3_7
  · exact absurd hs (by decide)
  · exact m13_8_3_9
  · exact absurd hs (by decide)
  · exact m13_8_3_11
  · exact m13_8_3_12

end Misses
