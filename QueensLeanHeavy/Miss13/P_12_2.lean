import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [12, 2]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_12_2_0_3 : go 13 7 9 [12, 2, 0, 3] = true := by decide +kernel
theorem m13_12_2_0_5 : go 13 7 9 [12, 2, 0, 5] = true := by decide +kernel
theorem m13_12_2_0_6 : go 13 7 9 [12, 2, 0, 6] = true := by decide +kernel
theorem m13_12_2_0_7 : go 13 7 9 [12, 2, 0, 7] = true := by decide +kernel
theorem m13_12_2_0_8 : go 13 7 9 [12, 2, 0, 8] = true := by decide +kernel
theorem m13_12_2_0_10 : go 13 7 9 [12, 2, 0, 10] = true := by decide +kernel
theorem m13_12_2_0_11 : go 13 7 9 [12, 2, 0, 11] = true := by decide +kernel

theorem m13_12_2_0 : go 13 7 10 [12, 2, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_0_3
  · exact absurd hs (by decide)
  · exact m13_12_2_0_5
  · exact m13_12_2_0_6
  · exact m13_12_2_0_7
  · exact m13_12_2_0_8
  · exact absurd hs (by decide)
  · exact m13_12_2_0_10
  · exact m13_12_2_0_11
  · exact absurd hs (by decide)

theorem m13_12_2_4_1 : go 13 7 9 [12, 2, 4, 1] = true := by decide +kernel
theorem m13_12_2_4_6 : go 13 7 9 [12, 2, 4, 6] = true := by decide +kernel
theorem m13_12_2_4_7 : go 13 7 9 [12, 2, 4, 7] = true := by decide +kernel
theorem m13_12_2_4_8 : go 13 7 9 [12, 2, 4, 8] = true := by decide +kernel
theorem m13_12_2_4_10 : go 13 7 9 [12, 2, 4, 10] = true := by decide +kernel
theorem m13_12_2_4_11 : go 13 7 9 [12, 2, 4, 11] = true := by decide +kernel

theorem m13_12_2_4 : go 13 7 10 [12, 2, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_4_6
  · exact m13_12_2_4_7
  · exact m13_12_2_4_8
  · exact absurd hs (by decide)
  · exact m13_12_2_4_10
  · exact m13_12_2_4_11
  · exact absurd hs (by decide)

theorem m13_12_2_5_1 : go 13 7 9 [12, 2, 5, 1] = true := by decide +kernel
theorem m13_12_2_5_3 : go 13 7 9 [12, 2, 5, 3] = true := by decide +kernel
theorem m13_12_2_5_7 : go 13 7 9 [12, 2, 5, 7] = true := by decide +kernel
theorem m13_12_2_5_8 : go 13 7 9 [12, 2, 5, 8] = true := by decide +kernel
theorem m13_12_2_5_10 : go 13 7 9 [12, 2, 5, 10] = true := by decide +kernel
theorem m13_12_2_5_11 : go 13 7 9 [12, 2, 5, 11] = true := by decide +kernel

theorem m13_12_2_5 : go 13 7 10 [12, 2, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_5_1
  · exact absurd hs (by decide)
  · exact m13_12_2_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_5_7
  · exact m13_12_2_5_8
  · exact absurd hs (by decide)
  · exact m13_12_2_5_10
  · exact m13_12_2_5_11
  · exact absurd hs (by decide)

theorem m13_12_2_6_1 : go 13 7 9 [12, 2, 6, 1] = true := by decide +kernel
theorem m13_12_2_6_3 : go 13 7 9 [12, 2, 6, 3] = true := by decide +kernel
theorem m13_12_2_6_8 : go 13 7 9 [12, 2, 6, 8] = true := by decide +kernel
theorem m13_12_2_6_10 : go 13 7 9 [12, 2, 6, 10] = true := by decide +kernel
theorem m13_12_2_6_11 : go 13 7 9 [12, 2, 6, 11] = true := by decide +kernel

theorem m13_12_2_6 : go 13 7 10 [12, 2, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_6_1
  · exact absurd hs (by decide)
  · exact m13_12_2_6_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_6_8
  · exact absurd hs (by decide)
  · exact m13_12_2_6_10
  · exact m13_12_2_6_11
  · exact absurd hs (by decide)

theorem m13_12_2_7_1 : go 13 7 9 [12, 2, 7, 1] = true := by decide +kernel
theorem m13_12_2_7_3 : go 13 7 9 [12, 2, 7, 3] = true := by decide +kernel
theorem m13_12_2_7_5 : go 13 7 9 [12, 2, 7, 5] = true := by decide +kernel
theorem m13_12_2_7_10 : go 13 7 9 [12, 2, 7, 10] = true := by decide +kernel
theorem m13_12_2_7_11 : go 13 7 9 [12, 2, 7, 11] = true := by decide +kernel

theorem m13_12_2_7 : go 13 7 10 [12, 2, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_7_1
  · exact absurd hs (by decide)
  · exact m13_12_2_7_3
  · exact absurd hs (by decide)
  · exact m13_12_2_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_7_10
  · exact m13_12_2_7_11
  · exact absurd hs (by decide)

theorem m13_12_2_8_1 : go 13 7 9 [12, 2, 8, 1] = true := by decide +kernel
theorem m13_12_2_8_3 : go 13 7 9 [12, 2, 8, 3] = true := by decide +kernel
theorem m13_12_2_8_5 : go 13 7 9 [12, 2, 8, 5] = true := by decide +kernel
theorem m13_12_2_8_6 : go 13 7 9 [12, 2, 8, 6] = true := by decide +kernel
theorem m13_12_2_8_10 : go 13 7 9 [12, 2, 8, 10] = true := by decide +kernel
theorem m13_12_2_8_11 : go 13 7 9 [12, 2, 8, 11] = true := by decide +kernel

theorem m13_12_2_8 : go 13 7 10 [12, 2, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_8_1
  · exact absurd hs (by decide)
  · exact m13_12_2_8_3
  · exact absurd hs (by decide)
  · exact m13_12_2_8_5
  · exact m13_12_2_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_8_10
  · exact m13_12_2_8_11
  · exact absurd hs (by decide)

theorem m13_12_2_9_1 : go 13 7 9 [12, 2, 9, 1] = true := by decide +kernel
theorem m13_12_2_9_3 : go 13 7 9 [12, 2, 9, 3] = true := by decide +kernel
theorem m13_12_2_9_5 : go 13 7 9 [12, 2, 9, 5] = true := by decide +kernel
theorem m13_12_2_9_6 : go 13 7 9 [12, 2, 9, 6] = true := by decide +kernel
theorem m13_12_2_9_7 : go 13 7 9 [12, 2, 9, 7] = true := by decide +kernel
theorem m13_12_2_9_11 : go 13 7 9 [12, 2, 9, 11] = true := by decide +kernel

theorem m13_12_2_9 : go 13 7 10 [12, 2, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_9_1
  · exact absurd hs (by decide)
  · exact m13_12_2_9_3
  · exact absurd hs (by decide)
  · exact m13_12_2_9_5
  · exact m13_12_2_9_6
  · exact m13_12_2_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_9_11
  · exact absurd hs (by decide)

theorem m13_12_2_11_1 : go 13 7 9 [12, 2, 11, 1] = true := by decide +kernel
theorem m13_12_2_11_3 : go 13 7 9 [12, 2, 11, 3] = true := by decide +kernel
theorem m13_12_2_11_5 : go 13 7 9 [12, 2, 11, 5] = true := by decide +kernel
theorem m13_12_2_11_6 : go 13 7 9 [12, 2, 11, 6] = true := by decide +kernel
theorem m13_12_2_11_7 : go 13 7 9 [12, 2, 11, 7] = true := by decide +kernel
theorem m13_12_2_11_8 : go 13 7 9 [12, 2, 11, 8] = true := by decide +kernel

theorem m13_12_2_11 : go 13 7 10 [12, 2, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_12_2_11_1
  · exact absurd hs (by decide)
  · exact m13_12_2_11_3
  · exact absurd hs (by decide)
  · exact m13_12_2_11_5
  · exact m13_12_2_11_6
  · exact m13_12_2_11_7
  · exact m13_12_2_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_12_2 : go 13 7 11 [12, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_12_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_12_2_4
  · exact m13_12_2_5
  · exact m13_12_2_6
  · exact m13_12_2_7
  · exact m13_12_2_8
  · exact m13_12_2_9
  · exact absurd hs (by decide)
  · exact m13_12_2_11
  · exact absurd hs (by decide)

end Misses
