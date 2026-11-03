import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 3]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_3_0_2 : go 13 7 9 [12, 3, 0, 2] = true := by decide +kernel
theorem m13_12_3_0_4 : go 13 7 9 [12, 3, 0, 4] = true := by decide +kernel
theorem m13_12_3_0_6 : go 13 7 9 [12, 3, 0, 6] = true := by decide +kernel
theorem m13_12_3_0_7 : go 13 7 9 [12, 3, 0, 7] = true := by decide +kernel
theorem m13_12_3_0_8 : go 13 7 9 [12, 3, 0, 8] = true := by decide +kernel
theorem m13_12_3_0_10 : go 13 7 9 [12, 3, 0, 10] = true := by decide +kernel
theorem m13_12_3_0_11 : go 13 7 9 [12, 3, 0, 11] = true := by decide +kernel

theorem m13_12_3_0 : go 13 7 10 [12, 3, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_0_2
  · exact absurd hs (by decide)
  · exact m13_12_3_0_4
  · exact absurd hs (by decide)
  · exact m13_12_3_0_6
  · exact m13_12_3_0_7
  · exact m13_12_3_0_8
  · exact absurd hs (by decide)
  · exact m13_12_3_0_10
  · exact m13_12_3_0_11
  · exact absurd hs (by decide)

theorem m13_12_3_1_4 : go 13 7 9 [12, 3, 1, 4] = true := by decide +kernel
theorem m13_12_3_1_6 : go 13 7 9 [12, 3, 1, 6] = true := by decide +kernel
theorem m13_12_3_1_7 : go 13 7 9 [12, 3, 1, 7] = true := by decide +kernel
theorem m13_12_3_1_8 : go 13 7 9 [12, 3, 1, 8] = true := by decide +kernel
theorem m13_12_3_1_10 : go 13 7 9 [12, 3, 1, 10] = true := by decide +kernel
theorem m13_12_3_1_11 : go 13 7 9 [12, 3, 1, 11] = true := by decide +kernel

theorem m13_12_3_1 : go 13 7 10 [12, 3, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_1_4
  · exact absurd hs (by decide)
  · exact m13_12_3_1_6
  · exact m13_12_3_1_7
  · exact m13_12_3_1_8
  · exact absurd hs (by decide)
  · exact m13_12_3_1_10
  · exact m13_12_3_1_11
  · exact absurd hs (by decide)

theorem m13_12_3_5_0 : go 13 7 9 [12, 3, 5, 0] = true := by decide +kernel
theorem m13_12_3_5_2 : go 13 7 9 [12, 3, 5, 2] = true := by decide +kernel
theorem m13_12_3_5_7 : go 13 7 9 [12, 3, 5, 7] = true := by decide +kernel
theorem m13_12_3_5_8 : go 13 7 9 [12, 3, 5, 8] = true := by decide +kernel
theorem m13_12_3_5_10 : go 13 7 9 [12, 3, 5, 10] = true := by decide +kernel
theorem m13_12_3_5_11 : go 13 7 9 [12, 3, 5, 11] = true := by decide +kernel

theorem m13_12_3_5 : go 13 7 10 [12, 3, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_5_0
  · exact absurd hs (by decide)
  · exact m13_12_3_5_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_5_7
  · exact m13_12_3_5_8
  · exact absurd hs (by decide)
  · exact m13_12_3_5_10
  · exact m13_12_3_5_11
  · exact absurd hs (by decide)

theorem m13_12_3_6_0 : go 13 7 9 [12, 3, 6, 0] = true := by decide +kernel
theorem m13_12_3_6_2 : go 13 7 9 [12, 3, 6, 2] = true := by decide +kernel
theorem m13_12_3_6_4 : go 13 7 9 [12, 3, 6, 4] = true := by decide +kernel
theorem m13_12_3_6_8 : go 13 7 9 [12, 3, 6, 8] = true := by decide +kernel
theorem m13_12_3_6_10 : go 13 7 9 [12, 3, 6, 10] = true := by decide +kernel
theorem m13_12_3_6_11 : go 13 7 9 [12, 3, 6, 11] = true := by decide +kernel

theorem m13_12_3_6 : go 13 7 10 [12, 3, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_6_0
  · exact absurd hs (by decide)
  · exact m13_12_3_6_2
  · exact absurd hs (by decide)
  · exact m13_12_3_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_6_8
  · exact absurd hs (by decide)
  · exact m13_12_3_6_10
  · exact m13_12_3_6_11
  · exact absurd hs (by decide)

theorem m13_12_3_7_0 : go 13 7 9 [12, 3, 7, 0] = true := by decide +kernel
theorem m13_12_3_7_2 : go 13 7 9 [12, 3, 7, 2] = true := by decide +kernel
theorem m13_12_3_7_4 : go 13 7 9 [12, 3, 7, 4] = true := by decide +kernel
theorem m13_12_3_7_10 : go 13 7 9 [12, 3, 7, 10] = true := by decide +kernel
theorem m13_12_3_7_11 : go 13 7 9 [12, 3, 7, 11] = true := by decide +kernel

theorem m13_12_3_7 : go 13 7 10 [12, 3, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_7_0
  · exact absurd hs (by decide)
  · exact m13_12_3_7_2
  · exact absurd hs (by decide)
  · exact m13_12_3_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_7_10
  · exact m13_12_3_7_11
  · exact absurd hs (by decide)

theorem m13_12_3_8_0 : go 13 7 9 [12, 3, 8, 0] = true := by decide +kernel
theorem m13_12_3_8_2 : go 13 7 9 [12, 3, 8, 2] = true := by decide +kernel
theorem m13_12_3_8_4 : go 13 7 9 [12, 3, 8, 4] = true := by decide +kernel
theorem m13_12_3_8_6 : go 13 7 9 [12, 3, 8, 6] = true := by decide +kernel
theorem m13_12_3_8_10 : go 13 7 9 [12, 3, 8, 10] = true := by decide +kernel
theorem m13_12_3_8_11 : go 13 7 9 [12, 3, 8, 11] = true := by decide +kernel

theorem m13_12_3_8 : go 13 7 10 [12, 3, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_8_0
  · exact absurd hs (by decide)
  · exact m13_12_3_8_2
  · exact absurd hs (by decide)
  · exact m13_12_3_8_4
  · exact absurd hs (by decide)
  · exact m13_12_3_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_8_10
  · exact m13_12_3_8_11
  · exact absurd hs (by decide)

theorem m13_12_3_9_0 : go 13 7 9 [12, 3, 9, 0] = true := by decide +kernel
theorem m13_12_3_9_2 : go 13 7 9 [12, 3, 9, 2] = true := by decide +kernel
theorem m13_12_3_9_4 : go 13 7 9 [12, 3, 9, 4] = true := by decide +kernel
theorem m13_12_3_9_6 : go 13 7 9 [12, 3, 9, 6] = true := by decide +kernel
theorem m13_12_3_9_7 : go 13 7 9 [12, 3, 9, 7] = true := by decide +kernel
theorem m13_12_3_9_11 : go 13 7 9 [12, 3, 9, 11] = true := by decide +kernel

theorem m13_12_3_9 : go 13 7 10 [12, 3, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_9_0
  · exact absurd hs (by decide)
  · exact m13_12_3_9_2
  · exact absurd hs (by decide)
  · exact m13_12_3_9_4
  · exact absurd hs (by decide)
  · exact m13_12_3_9_6
  · exact m13_12_3_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_9_11
  · exact absurd hs (by decide)

theorem m13_12_3_11_0 : go 13 7 9 [12, 3, 11, 0] = true := by decide +kernel
theorem m13_12_3_11_2 : go 13 7 9 [12, 3, 11, 2] = true := by decide +kernel
theorem m13_12_3_11_4 : go 13 7 9 [12, 3, 11, 4] = true := by decide +kernel
theorem m13_12_3_11_6 : go 13 7 9 [12, 3, 11, 6] = true := by decide +kernel
theorem m13_12_3_11_7 : go 13 7 9 [12, 3, 11, 7] = true := by decide +kernel
theorem m13_12_3_11_8 : go 13 7 9 [12, 3, 11, 8] = true := by decide +kernel

theorem m13_12_3_11 : go 13 7 10 [12, 3, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_11_0
  · exact absurd hs (by decide)
  · exact m13_12_3_11_2
  · exact absurd hs (by decide)
  · exact m13_12_3_11_4
  · exact absurd hs (by decide)
  · exact m13_12_3_11_6
  · exact m13_12_3_11_7
  · exact m13_12_3_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_3 : go 13 7 11 [12, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_3_0
  · exact m13_12_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_3_5
  · exact m13_12_3_6
  · exact m13_12_3_7
  · exact m13_12_3_8
  · exact m13_12_3_9
  · exact absurd hs (by decide)
  · exact m13_12_3_11
  · exact absurd hs (by decide)

end Misses
