import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_0_2_4 : go 13 7 9 [12, 0, 2, 4] = true := by decide +kernel
theorem m13_12_0_2_5 : go 13 7 9 [12, 0, 2, 5] = true := by decide +kernel
theorem m13_12_0_2_6 : go 13 7 9 [12, 0, 2, 6] = true := by decide +kernel
theorem m13_12_0_2_7 : go 13 7 9 [12, 0, 2, 7] = true := by decide +kernel
theorem m13_12_0_2_8 : go 13 7 9 [12, 0, 2, 8] = true := by decide +kernel
theorem m13_12_0_2_10 : go 13 7 9 [12, 0, 2, 10] = true := by decide +kernel
theorem m13_12_0_2_11 : go 13 7 9 [12, 0, 2, 11] = true := by decide +kernel

theorem m13_12_0_2 : go 13 7 10 [12, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_2_4
  · exact m13_12_0_2_5
  · exact m13_12_0_2_6
  · exact m13_12_0_2_7
  · exact m13_12_0_2_8
  · exact absurd hs (by decide)
  · exact m13_12_0_2_10
  · exact m13_12_0_2_11
  · exact absurd hs (by decide)

theorem m13_12_0_3_1 : go 13 7 9 [12, 0, 3, 1] = true := by decide +kernel
theorem m13_12_0_3_5 : go 13 7 9 [12, 0, 3, 5] = true := by decide +kernel
theorem m13_12_0_3_6 : go 13 7 9 [12, 0, 3, 6] = true := by decide +kernel
theorem m13_12_0_3_7 : go 13 7 9 [12, 0, 3, 7] = true := by decide +kernel
theorem m13_12_0_3_8 : go 13 7 9 [12, 0, 3, 8] = true := by decide +kernel
theorem m13_12_0_3_10 : go 13 7 9 [12, 0, 3, 10] = true := by decide +kernel
theorem m13_12_0_3_11 : go 13 7 9 [12, 0, 3, 11] = true := by decide +kernel

theorem m13_12_0_3 : go 13 7 10 [12, 0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_3_5
  · exact m13_12_0_3_6
  · exact m13_12_0_3_7
  · exact m13_12_0_3_8
  · exact absurd hs (by decide)
  · exact m13_12_0_3_10
  · exact m13_12_0_3_11
  · exact absurd hs (by decide)

theorem m13_12_0_4_1 : go 13 7 9 [12, 0, 4, 1] = true := by decide +kernel
theorem m13_12_0_4_6 : go 13 7 9 [12, 0, 4, 6] = true := by decide +kernel
theorem m13_12_0_4_7 : go 13 7 9 [12, 0, 4, 7] = true := by decide +kernel
theorem m13_12_0_4_8 : go 13 7 9 [12, 0, 4, 8] = true := by decide +kernel
theorem m13_12_0_4_10 : go 13 7 9 [12, 0, 4, 10] = true := by decide +kernel
theorem m13_12_0_4_11 : go 13 7 9 [12, 0, 4, 11] = true := by decide +kernel

theorem m13_12_0_4 : go 13 7 10 [12, 0, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_4_6
  · exact m13_12_0_4_7
  · exact m13_12_0_4_8
  · exact absurd hs (by decide)
  · exact m13_12_0_4_10
  · exact m13_12_0_4_11
  · exact absurd hs (by decide)

theorem m13_12_0_5_1 : go 13 7 9 [12, 0, 5, 1] = true := by decide +kernel
theorem m13_12_0_5_3 : go 13 7 9 [12, 0, 5, 3] = true := by decide +kernel
theorem m13_12_0_5_7 : go 13 7 9 [12, 0, 5, 7] = true := by decide +kernel
theorem m13_12_0_5_8 : go 13 7 9 [12, 0, 5, 8] = true := by decide +kernel
theorem m13_12_0_5_10 : go 13 7 9 [12, 0, 5, 10] = true := by decide +kernel
theorem m13_12_0_5_11 : go 13 7 9 [12, 0, 5, 11] = true := by decide +kernel

theorem m13_12_0_5 : go 13 7 10 [12, 0, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_5_1
  · exact absurd hs (by decide)
  · exact m13_12_0_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_5_7
  · exact m13_12_0_5_8
  · exact absurd hs (by decide)
  · exact m13_12_0_5_10
  · exact m13_12_0_5_11
  · exact absurd hs (by decide)

theorem m13_12_0_6_1 : go 13 7 9 [12, 0, 6, 1] = true := by decide +kernel
theorem m13_12_0_6_3 : go 13 7 9 [12, 0, 6, 3] = true := by decide +kernel
theorem m13_12_0_6_4 : go 13 7 9 [12, 0, 6, 4] = true := by decide +kernel
theorem m13_12_0_6_8 : go 13 7 9 [12, 0, 6, 8] = true := by decide +kernel
theorem m13_12_0_6_10 : go 13 7 9 [12, 0, 6, 10] = true := by decide +kernel
theorem m13_12_0_6_11 : go 13 7 9 [12, 0, 6, 11] = true := by decide +kernel

theorem m13_12_0_6 : go 13 7 10 [12, 0, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_6_1
  · exact absurd hs (by decide)
  · exact m13_12_0_6_3
  · exact m13_12_0_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_6_8
  · exact absurd hs (by decide)
  · exact m13_12_0_6_10
  · exact m13_12_0_6_11
  · exact absurd hs (by decide)

theorem m13_12_0_7_1 : go 13 7 9 [12, 0, 7, 1] = true := by decide +kernel
theorem m13_12_0_7_3 : go 13 7 9 [12, 0, 7, 3] = true := by decide +kernel
theorem m13_12_0_7_4 : go 13 7 9 [12, 0, 7, 4] = true := by decide +kernel
theorem m13_12_0_7_5 : go 13 7 9 [12, 0, 7, 5] = true := by decide +kernel
theorem m13_12_0_7_10 : go 13 7 9 [12, 0, 7, 10] = true := by decide +kernel
theorem m13_12_0_7_11 : go 13 7 9 [12, 0, 7, 11] = true := by decide +kernel

theorem m13_12_0_7 : go 13 7 10 [12, 0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_7_1
  · exact absurd hs (by decide)
  · exact m13_12_0_7_3
  · exact m13_12_0_7_4
  · exact m13_12_0_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_7_10
  · exact m13_12_0_7_11
  · exact absurd hs (by decide)

theorem m13_12_0_8_1 : go 13 7 9 [12, 0, 8, 1] = true := by decide +kernel
theorem m13_12_0_8_3 : go 13 7 9 [12, 0, 8, 3] = true := by decide +kernel
theorem m13_12_0_8_4 : go 13 7 9 [12, 0, 8, 4] = true := by decide +kernel
theorem m13_12_0_8_5 : go 13 7 9 [12, 0, 8, 5] = true := by decide +kernel
theorem m13_12_0_8_6 : go 13 7 9 [12, 0, 8, 6] = true := by decide +kernel
theorem m13_12_0_8_10 : go 13 7 9 [12, 0, 8, 10] = true := by decide +kernel
theorem m13_12_0_8_11 : go 13 7 9 [12, 0, 8, 11] = true := by decide +kernel

theorem m13_12_0_8 : go 13 7 10 [12, 0, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_8_1
  · exact absurd hs (by decide)
  · exact m13_12_0_8_3
  · exact m13_12_0_8_4
  · exact m13_12_0_8_5
  · exact m13_12_0_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_8_10
  · exact m13_12_0_8_11
  · exact absurd hs (by decide)

theorem m13_12_0_9_1 : go 13 7 9 [12, 0, 9, 1] = true := by decide +kernel
theorem m13_12_0_9_3 : go 13 7 9 [12, 0, 9, 3] = true := by decide +kernel
theorem m13_12_0_9_4 : go 13 7 9 [12, 0, 9, 4] = true := by decide +kernel
theorem m13_12_0_9_5 : go 13 7 9 [12, 0, 9, 5] = true := by decide +kernel
theorem m13_12_0_9_6 : go 13 7 9 [12, 0, 9, 6] = true := by decide +kernel
theorem m13_12_0_9_7 : go 13 7 9 [12, 0, 9, 7] = true := by decide +kernel
theorem m13_12_0_9_11 : go 13 7 9 [12, 0, 9, 11] = true := by decide +kernel

theorem m13_12_0_9 : go 13 7 10 [12, 0, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_9_1
  · exact absurd hs (by decide)
  · exact m13_12_0_9_3
  · exact m13_12_0_9_4
  · exact m13_12_0_9_5
  · exact m13_12_0_9_6
  · exact m13_12_0_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_9_11
  · exact absurd hs (by decide)

theorem m13_12_0_11_1 : go 13 7 9 [12, 0, 11, 1] = true := by decide +kernel
theorem m13_12_0_11_3 : go 13 7 9 [12, 0, 11, 3] = true := by decide +kernel
theorem m13_12_0_11_4 : go 13 7 9 [12, 0, 11, 4] = true := by decide +kernel
theorem m13_12_0_11_5 : go 13 7 9 [12, 0, 11, 5] = true := by decide +kernel
theorem m13_12_0_11_6 : go 13 7 9 [12, 0, 11, 6] = true := by decide +kernel
theorem m13_12_0_11_7 : go 13 7 9 [12, 0, 11, 7] = true := by decide +kernel
theorem m13_12_0_11_8 : go 13 7 9 [12, 0, 11, 8] = true := by decide +kernel

theorem m13_12_0_11 : go 13 7 10 [12, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_0_11_1
  · exact absurd hs (by decide)
  · exact m13_12_0_11_3
  · exact m13_12_0_11_4
  · exact m13_12_0_11_5
  · exact m13_12_0_11_6
  · exact m13_12_0_11_7
  · exact m13_12_0_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_0 : go 13 7 11 [12, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_0_2
  · exact m13_12_0_3
  · exact m13_12_0_4
  · exact m13_12_0_5
  · exact m13_12_0_6
  · exact m13_12_0_7
  · exact m13_12_0_8
  · exact m13_12_0_9
  · exact absurd hs (by decide)
  · exact m13_12_0_11
  · exact absurd hs (by decide)

end Misses
