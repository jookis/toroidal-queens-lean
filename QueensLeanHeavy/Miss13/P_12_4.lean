import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 4]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_4_0_3 : go 13 7 9 [12, 4, 0, 3] = true := by decide +kernel
theorem m13_12_4_0_5 : go 13 7 9 [12, 4, 0, 5] = true := by decide +kernel
theorem m13_12_4_0_7 : go 13 7 9 [12, 4, 0, 7] = true := by decide +kernel
theorem m13_12_4_0_8 : go 13 7 9 [12, 4, 0, 8] = true := by decide +kernel
theorem m13_12_4_0_10 : go 13 7 9 [12, 4, 0, 10] = true := by decide +kernel
theorem m13_12_4_0_11 : go 13 7 9 [12, 4, 0, 11] = true := by decide +kernel

theorem m13_12_4_0 : go 13 7 10 [12, 4, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_0_3
  · exact absurd hs (by decide)
  · exact m13_12_4_0_5
  · exact absurd hs (by decide)
  · exact m13_12_4_0_7
  · exact m13_12_4_0_8
  · exact absurd hs (by decide)
  · exact m13_12_4_0_10
  · exact m13_12_4_0_11
  · exact absurd hs (by decide)

theorem m13_12_4_1_3 : go 13 7 9 [12, 4, 1, 3] = true := by decide +kernel
theorem m13_12_4_1_5 : go 13 7 9 [12, 4, 1, 5] = true := by decide +kernel
theorem m13_12_4_1_7 : go 13 7 9 [12, 4, 1, 7] = true := by decide +kernel
theorem m13_12_4_1_8 : go 13 7 9 [12, 4, 1, 8] = true := by decide +kernel
theorem m13_12_4_1_10 : go 13 7 9 [12, 4, 1, 10] = true := by decide +kernel
theorem m13_12_4_1_11 : go 13 7 9 [12, 4, 1, 11] = true := by decide +kernel

theorem m13_12_4_1 : go 13 7 10 [12, 4, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_1_3
  · exact absurd hs (by decide)
  · exact m13_12_4_1_5
  · exact absurd hs (by decide)
  · exact m13_12_4_1_7
  · exact m13_12_4_1_8
  · exact absurd hs (by decide)
  · exact m13_12_4_1_10
  · exact m13_12_4_1_11
  · exact absurd hs (by decide)

theorem m13_12_4_2_0 : go 13 7 9 [12, 4, 2, 0] = true := by decide +kernel
theorem m13_12_4_2_5 : go 13 7 9 [12, 4, 2, 5] = true := by decide +kernel
theorem m13_12_4_2_7 : go 13 7 9 [12, 4, 2, 7] = true := by decide +kernel
theorem m13_12_4_2_8 : go 13 7 9 [12, 4, 2, 8] = true := by decide +kernel
theorem m13_12_4_2_10 : go 13 7 9 [12, 4, 2, 10] = true := by decide +kernel
theorem m13_12_4_2_11 : go 13 7 9 [12, 4, 2, 11] = true := by decide +kernel

theorem m13_12_4_2 : go 13 7 10 [12, 4, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_2_5
  · exact absurd hs (by decide)
  · exact m13_12_4_2_7
  · exact m13_12_4_2_8
  · exact absurd hs (by decide)
  · exact m13_12_4_2_10
  · exact m13_12_4_2_11
  · exact absurd hs (by decide)

theorem m13_12_4_6_0 : go 13 7 9 [12, 4, 6, 0] = true := by decide +kernel
theorem m13_12_4_6_1 : go 13 7 9 [12, 4, 6, 1] = true := by decide +kernel
theorem m13_12_4_6_3 : go 13 7 9 [12, 4, 6, 3] = true := by decide +kernel
theorem m13_12_4_6_8 : go 13 7 9 [12, 4, 6, 8] = true := by decide +kernel
theorem m13_12_4_6_10 : go 13 7 9 [12, 4, 6, 10] = true := by decide +kernel
theorem m13_12_4_6_11 : go 13 7 9 [12, 4, 6, 11] = true := by decide +kernel

theorem m13_12_4_6 : go 13 7 10 [12, 4, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_6_0
  · exact m13_12_4_6_1
  · exact absurd hs (by decide)
  · exact m13_12_4_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_6_8
  · exact absurd hs (by decide)
  · exact m13_12_4_6_10
  · exact m13_12_4_6_11
  · exact absurd hs (by decide)

theorem m13_12_4_7_0 : go 13 7 9 [12, 4, 7, 0] = true := by decide +kernel
theorem m13_12_4_7_1 : go 13 7 9 [12, 4, 7, 1] = true := by decide +kernel
theorem m13_12_4_7_3 : go 13 7 9 [12, 4, 7, 3] = true := by decide +kernel
theorem m13_12_4_7_5 : go 13 7 9 [12, 4, 7, 5] = true := by decide +kernel
theorem m13_12_4_7_10 : go 13 7 9 [12, 4, 7, 10] = true := by decide +kernel
theorem m13_12_4_7_11 : go 13 7 9 [12, 4, 7, 11] = true := by decide +kernel

theorem m13_12_4_7 : go 13 7 10 [12, 4, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_7_0
  · exact m13_12_4_7_1
  · exact absurd hs (by decide)
  · exact m13_12_4_7_3
  · exact absurd hs (by decide)
  · exact m13_12_4_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_7_10
  · exact m13_12_4_7_11
  · exact absurd hs (by decide)

theorem m13_12_4_8_0 : go 13 7 9 [12, 4, 8, 0] = true := by decide +kernel
theorem m13_12_4_8_1 : go 13 7 9 [12, 4, 8, 1] = true := by decide +kernel
theorem m13_12_4_8_3 : go 13 7 9 [12, 4, 8, 3] = true := by decide +kernel
theorem m13_12_4_8_5 : go 13 7 9 [12, 4, 8, 5] = true := by decide +kernel
theorem m13_12_4_8_10 : go 13 7 9 [12, 4, 8, 10] = true := by decide +kernel
theorem m13_12_4_8_11 : go 13 7 9 [12, 4, 8, 11] = true := by decide +kernel

theorem m13_12_4_8 : go 13 7 10 [12, 4, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_8_0
  · exact m13_12_4_8_1
  · exact absurd hs (by decide)
  · exact m13_12_4_8_3
  · exact absurd hs (by decide)
  · exact m13_12_4_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_8_10
  · exact m13_12_4_8_11
  · exact absurd hs (by decide)

theorem m13_12_4_9_0 : go 13 7 9 [12, 4, 9, 0] = true := by decide +kernel
theorem m13_12_4_9_1 : go 13 7 9 [12, 4, 9, 1] = true := by decide +kernel
theorem m13_12_4_9_3 : go 13 7 9 [12, 4, 9, 3] = true := by decide +kernel
theorem m13_12_4_9_5 : go 13 7 9 [12, 4, 9, 5] = true := by decide +kernel
theorem m13_12_4_9_7 : go 13 7 9 [12, 4, 9, 7] = true := by decide +kernel
theorem m13_12_4_9_11 : go 13 7 9 [12, 4, 9, 11] = true := by decide +kernel

theorem m13_12_4_9 : go 13 7 10 [12, 4, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_9_0
  · exact m13_12_4_9_1
  · exact absurd hs (by decide)
  · exact m13_12_4_9_3
  · exact absurd hs (by decide)
  · exact m13_12_4_9_5
  · exact absurd hs (by decide)
  · exact m13_12_4_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_9_11
  · exact absurd hs (by decide)

theorem m13_12_4_11_0 : go 13 7 9 [12, 4, 11, 0] = true := by decide +kernel
theorem m13_12_4_11_1 : go 13 7 9 [12, 4, 11, 1] = true := by decide +kernel
theorem m13_12_4_11_3 : go 13 7 9 [12, 4, 11, 3] = true := by decide +kernel
theorem m13_12_4_11_5 : go 13 7 9 [12, 4, 11, 5] = true := by decide +kernel
theorem m13_12_4_11_7 : go 13 7 9 [12, 4, 11, 7] = true := by decide +kernel
theorem m13_12_4_11_8 : go 13 7 9 [12, 4, 11, 8] = true := by decide +kernel

theorem m13_12_4_11 : go 13 7 10 [12, 4, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_11_0
  · exact m13_12_4_11_1
  · exact absurd hs (by decide)
  · exact m13_12_4_11_3
  · exact absurd hs (by decide)
  · exact m13_12_4_11_5
  · exact absurd hs (by decide)
  · exact m13_12_4_11_7
  · exact m13_12_4_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_4 : go 13 7 11 [12, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_4_0
  · exact m13_12_4_1
  · exact m13_12_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_4_6
  · exact m13_12_4_7
  · exact m13_12_4_8
  · exact m13_12_4_9
  · exact absurd hs (by decide)
  · exact m13_12_4_11
  · exact absurd hs (by decide)

end Misses
