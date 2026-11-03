import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 5]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_5_0_2 : go 13 7 9 [12, 5, 0, 2] = true := by decide +kernel
theorem m13_12_5_0_4 : go 13 7 9 [12, 5, 0, 4] = true := by decide +kernel
theorem m13_12_5_0_6 : go 13 7 9 [12, 5, 0, 6] = true := by decide +kernel
theorem m13_12_5_0_8 : go 13 7 9 [12, 5, 0, 8] = true := by decide +kernel
theorem m13_12_5_0_10 : go 13 7 9 [12, 5, 0, 10] = true := by decide +kernel
theorem m13_12_5_0_11 : go 13 7 9 [12, 5, 0, 11] = true := by decide +kernel

theorem m13_12_5_0 : go 13 7 10 [12, 5, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_0_2
  · exact absurd hs (by decide)
  · exact m13_12_5_0_4
  · exact absurd hs (by decide)
  · exact m13_12_5_0_6
  · exact absurd hs (by decide)
  · exact m13_12_5_0_8
  · exact absurd hs (by decide)
  · exact m13_12_5_0_10
  · exact m13_12_5_0_11
  · exact absurd hs (by decide)

theorem m13_12_5_1_4 : go 13 7 9 [12, 5, 1, 4] = true := by decide +kernel
theorem m13_12_5_1_6 : go 13 7 9 [12, 5, 1, 6] = true := by decide +kernel
theorem m13_12_5_1_8 : go 13 7 9 [12, 5, 1, 8] = true := by decide +kernel
theorem m13_12_5_1_10 : go 13 7 9 [12, 5, 1, 10] = true := by decide +kernel
theorem m13_12_5_1_11 : go 13 7 9 [12, 5, 1, 11] = true := by decide +kernel

theorem m13_12_5_1 : go 13 7 10 [12, 5, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_1_4
  · exact absurd hs (by decide)
  · exact m13_12_5_1_6
  · exact absurd hs (by decide)
  · exact m13_12_5_1_8
  · exact absurd hs (by decide)
  · exact m13_12_5_1_10
  · exact m13_12_5_1_11
  · exact absurd hs (by decide)

theorem m13_12_5_2_0 : go 13 7 9 [12, 5, 2, 0] = true := by decide +kernel
theorem m13_12_5_2_4 : go 13 7 9 [12, 5, 2, 4] = true := by decide +kernel
theorem m13_12_5_2_6 : go 13 7 9 [12, 5, 2, 6] = true := by decide +kernel
theorem m13_12_5_2_8 : go 13 7 9 [12, 5, 2, 8] = true := by decide +kernel
theorem m13_12_5_2_10 : go 13 7 9 [12, 5, 2, 10] = true := by decide +kernel
theorem m13_12_5_2_11 : go 13 7 9 [12, 5, 2, 11] = true := by decide +kernel

theorem m13_12_5_2 : go 13 7 10 [12, 5, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_2_4
  · exact absurd hs (by decide)
  · exact m13_12_5_2_6
  · exact absurd hs (by decide)
  · exact m13_12_5_2_8
  · exact absurd hs (by decide)
  · exact m13_12_5_2_10
  · exact m13_12_5_2_11
  · exact absurd hs (by decide)

theorem m13_12_5_3_0 : go 13 7 9 [12, 5, 3, 0] = true := by decide +kernel
theorem m13_12_5_3_1 : go 13 7 9 [12, 5, 3, 1] = true := by decide +kernel
theorem m13_12_5_3_6 : go 13 7 9 [12, 5, 3, 6] = true := by decide +kernel
theorem m13_12_5_3_8 : go 13 7 9 [12, 5, 3, 8] = true := by decide +kernel
theorem m13_12_5_3_10 : go 13 7 9 [12, 5, 3, 10] = true := by decide +kernel
theorem m13_12_5_3_11 : go 13 7 9 [12, 5, 3, 11] = true := by decide +kernel

theorem m13_12_5_3 : go 13 7 10 [12, 5, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_3_0
  · exact m13_12_5_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_3_6
  · exact absurd hs (by decide)
  · exact m13_12_5_3_8
  · exact absurd hs (by decide)
  · exact m13_12_5_3_10
  · exact m13_12_5_3_11
  · exact absurd hs (by decide)

theorem m13_12_5_7_0 : go 13 7 9 [12, 5, 7, 0] = true := by decide +kernel
theorem m13_12_5_7_1 : go 13 7 9 [12, 5, 7, 1] = true := by decide +kernel
theorem m13_12_5_7_2 : go 13 7 9 [12, 5, 7, 2] = true := by decide +kernel
theorem m13_12_5_7_4 : go 13 7 9 [12, 5, 7, 4] = true := by decide +kernel
theorem m13_12_5_7_10 : go 13 7 9 [12, 5, 7, 10] = true := by decide +kernel
theorem m13_12_5_7_11 : go 13 7 9 [12, 5, 7, 11] = true := by decide +kernel

theorem m13_12_5_7 : go 13 7 10 [12, 5, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_7_0
  · exact m13_12_5_7_1
  · exact m13_12_5_7_2
  · exact absurd hs (by decide)
  · exact m13_12_5_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_7_10
  · exact m13_12_5_7_11
  · exact absurd hs (by decide)

theorem m13_12_5_8_0 : go 13 7 9 [12, 5, 8, 0] = true := by decide +kernel
theorem m13_12_5_8_1 : go 13 7 9 [12, 5, 8, 1] = true := by decide +kernel
theorem m13_12_5_8_2 : go 13 7 9 [12, 5, 8, 2] = true := by decide +kernel
theorem m13_12_5_8_4 : go 13 7 9 [12, 5, 8, 4] = true := by decide +kernel
theorem m13_12_5_8_6 : go 13 7 9 [12, 5, 8, 6] = true := by decide +kernel
theorem m13_12_5_8_10 : go 13 7 9 [12, 5, 8, 10] = true := by decide +kernel
theorem m13_12_5_8_11 : go 13 7 9 [12, 5, 8, 11] = true := by decide +kernel

theorem m13_12_5_8 : go 13 7 10 [12, 5, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_8_0
  · exact m13_12_5_8_1
  · exact m13_12_5_8_2
  · exact absurd hs (by decide)
  · exact m13_12_5_8_4
  · exact absurd hs (by decide)
  · exact m13_12_5_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_8_10
  · exact m13_12_5_8_11
  · exact absurd hs (by decide)

theorem m13_12_5_9_0 : go 13 7 9 [12, 5, 9, 0] = true := by decide +kernel
theorem m13_12_5_9_1 : go 13 7 9 [12, 5, 9, 1] = true := by decide +kernel
theorem m13_12_5_9_2 : go 13 7 9 [12, 5, 9, 2] = true := by decide +kernel
theorem m13_12_5_9_4 : go 13 7 9 [12, 5, 9, 4] = true := by decide +kernel
theorem m13_12_5_9_6 : go 13 7 9 [12, 5, 9, 6] = true := by decide +kernel
theorem m13_12_5_9_11 : go 13 7 9 [12, 5, 9, 11] = true := by decide +kernel

theorem m13_12_5_9 : go 13 7 10 [12, 5, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_9_0
  · exact m13_12_5_9_1
  · exact m13_12_5_9_2
  · exact absurd hs (by decide)
  · exact m13_12_5_9_4
  · exact absurd hs (by decide)
  · exact m13_12_5_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_9_11
  · exact absurd hs (by decide)

theorem m13_12_5_11_0 : go 13 7 9 [12, 5, 11, 0] = true := by decide +kernel
theorem m13_12_5_11_1 : go 13 7 9 [12, 5, 11, 1] = true := by decide +kernel
theorem m13_12_5_11_2 : go 13 7 9 [12, 5, 11, 2] = true := by decide +kernel
theorem m13_12_5_11_4 : go 13 7 9 [12, 5, 11, 4] = true := by decide +kernel
theorem m13_12_5_11_6 : go 13 7 9 [12, 5, 11, 6] = true := by decide +kernel
theorem m13_12_5_11_8 : go 13 7 9 [12, 5, 11, 8] = true := by decide +kernel

theorem m13_12_5_11 : go 13 7 10 [12, 5, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_11_0
  · exact m13_12_5_11_1
  · exact m13_12_5_11_2
  · exact absurd hs (by decide)
  · exact m13_12_5_11_4
  · exact absurd hs (by decide)
  · exact m13_12_5_11_6
  · exact absurd hs (by decide)
  · exact m13_12_5_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_5 : go 13 7 11 [12, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_5_0
  · exact m13_12_5_1
  · exact m13_12_5_2
  · exact m13_12_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_5_7
  · exact m13_12_5_8
  · exact m13_12_5_9
  · exact absurd hs (by decide)
  · exact m13_12_5_11
  · exact absurd hs (by decide)

end Misses
