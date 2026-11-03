import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [9, 11]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_9_11_0_2 : go 13 7 9 [9, 11, 0, 2] = true := by decide +kernel
theorem m13_9_11_0_3 : go 13 7 9 [9, 11, 0, 3] = true := by decide +kernel
theorem m13_9_11_0_4 : go 13 7 9 [9, 11, 0, 4] = true := by decide +kernel
theorem m13_9_11_0_5 : go 13 7 9 [9, 11, 0, 5] = true := by decide +kernel
theorem m13_9_11_0_7 : go 13 7 9 [9, 11, 0, 7] = true := by decide +kernel
theorem m13_9_11_0_8 : go 13 7 9 [9, 11, 0, 8] = true := by decide +kernel
theorem m13_9_11_0_10 : go 13 7 9 [9, 11, 0, 10] = true := by decide +kernel

theorem m13_9_11_0 : go 13 7 10 [9, 11, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_0_2
  · exact m13_9_11_0_3
  · exact m13_9_11_0_4
  · exact m13_9_11_0_5
  · exact absurd hs (by decide)
  · exact m13_9_11_0_7
  · exact m13_9_11_0_8
  · exact absurd hs (by decide)
  · exact m13_9_11_0_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_1_3 : go 13 7 9 [9, 11, 1, 3] = true := by decide +kernel
theorem m13_9_11_1_4 : go 13 7 9 [9, 11, 1, 4] = true := by decide +kernel
theorem m13_9_11_1_5 : go 13 7 9 [9, 11, 1, 5] = true := by decide +kernel
theorem m13_9_11_1_7 : go 13 7 9 [9, 11, 1, 7] = true := by decide +kernel
theorem m13_9_11_1_8 : go 13 7 9 [9, 11, 1, 8] = true := by decide +kernel
theorem m13_9_11_1_10 : go 13 7 9 [9, 11, 1, 10] = true := by decide +kernel

theorem m13_9_11_1 : go 13 7 10 [9, 11, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_1_3
  · exact m13_9_11_1_4
  · exact m13_9_11_1_5
  · exact absurd hs (by decide)
  · exact m13_9_11_1_7
  · exact m13_9_11_1_8
  · exact absurd hs (by decide)
  · exact m13_9_11_1_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_2_0 : go 13 7 9 [9, 11, 2, 0] = true := by decide +kernel
theorem m13_9_11_2_4 : go 13 7 9 [9, 11, 2, 4] = true := by decide +kernel
theorem m13_9_11_2_5 : go 13 7 9 [9, 11, 2, 5] = true := by decide +kernel
theorem m13_9_11_2_7 : go 13 7 9 [9, 11, 2, 7] = true := by decide +kernel
theorem m13_9_11_2_8 : go 13 7 9 [9, 11, 2, 8] = true := by decide +kernel
theorem m13_9_11_2_10 : go 13 7 9 [9, 11, 2, 10] = true := by decide +kernel

theorem m13_9_11_2 : go 13 7 10 [9, 11, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_2_4
  · exact m13_9_11_2_5
  · exact absurd hs (by decide)
  · exact m13_9_11_2_7
  · exact m13_9_11_2_8
  · exact absurd hs (by decide)
  · exact m13_9_11_2_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_3_0 : go 13 7 9 [9, 11, 3, 0] = true := by decide +kernel
theorem m13_9_11_3_1 : go 13 7 9 [9, 11, 3, 1] = true := by decide +kernel
theorem m13_9_11_3_5 : go 13 7 9 [9, 11, 3, 5] = true := by decide +kernel
theorem m13_9_11_3_7 : go 13 7 9 [9, 11, 3, 7] = true := by decide +kernel
theorem m13_9_11_3_8 : go 13 7 9 [9, 11, 3, 8] = true := by decide +kernel
theorem m13_9_11_3_10 : go 13 7 9 [9, 11, 3, 10] = true := by decide +kernel

theorem m13_9_11_3 : go 13 7 10 [9, 11, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_3_0
  · exact m13_9_11_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_3_5
  · exact absurd hs (by decide)
  · exact m13_9_11_3_7
  · exact m13_9_11_3_8
  · exact absurd hs (by decide)
  · exact m13_9_11_3_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_4_0 : go 13 7 9 [9, 11, 4, 0] = true := by decide +kernel
theorem m13_9_11_4_1 : go 13 7 9 [9, 11, 4, 1] = true := by decide +kernel
theorem m13_9_11_4_2 : go 13 7 9 [9, 11, 4, 2] = true := by decide +kernel
theorem m13_9_11_4_7 : go 13 7 9 [9, 11, 4, 7] = true := by decide +kernel
theorem m13_9_11_4_8 : go 13 7 9 [9, 11, 4, 8] = true := by decide +kernel
theorem m13_9_11_4_10 : go 13 7 9 [9, 11, 4, 10] = true := by decide +kernel

theorem m13_9_11_4 : go 13 7 10 [9, 11, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_4_0
  · exact m13_9_11_4_1
  · exact m13_9_11_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_4_7
  · exact m13_9_11_4_8
  · exact absurd hs (by decide)
  · exact m13_9_11_4_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_5_0 : go 13 7 9 [9, 11, 5, 0] = true := by decide +kernel
theorem m13_9_11_5_1 : go 13 7 9 [9, 11, 5, 1] = true := by decide +kernel
theorem m13_9_11_5_2 : go 13 7 9 [9, 11, 5, 2] = true := by decide +kernel
theorem m13_9_11_5_3 : go 13 7 9 [9, 11, 5, 3] = true := by decide +kernel
theorem m13_9_11_5_7 : go 13 7 9 [9, 11, 5, 7] = true := by decide +kernel
theorem m13_9_11_5_8 : go 13 7 9 [9, 11, 5, 8] = true := by decide +kernel
theorem m13_9_11_5_10 : go 13 7 9 [9, 11, 5, 10] = true := by decide +kernel

theorem m13_9_11_5 : go 13 7 10 [9, 11, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_5_0
  · exact m13_9_11_5_1
  · exact m13_9_11_5_2
  · exact m13_9_11_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_5_7
  · exact m13_9_11_5_8
  · exact absurd hs (by decide)
  · exact m13_9_11_5_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_6_0 : go 13 7 9 [9, 11, 6, 0] = true := by decide +kernel
theorem m13_9_11_6_1 : go 13 7 9 [9, 11, 6, 1] = true := by decide +kernel
theorem m13_9_11_6_2 : go 13 7 9 [9, 11, 6, 2] = true := by decide +kernel
theorem m13_9_11_6_3 : go 13 7 9 [9, 11, 6, 3] = true := by decide +kernel
theorem m13_9_11_6_4 : go 13 7 9 [9, 11, 6, 4] = true := by decide +kernel
theorem m13_9_11_6_8 : go 13 7 9 [9, 11, 6, 8] = true := by decide +kernel
theorem m13_9_11_6_10 : go 13 7 9 [9, 11, 6, 10] = true := by decide +kernel

theorem m13_9_11_6 : go 13 7 10 [9, 11, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_6_0
  · exact m13_9_11_6_1
  · exact m13_9_11_6_2
  · exact m13_9_11_6_3
  · exact m13_9_11_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_6_8
  · exact absurd hs (by decide)
  · exact m13_9_11_6_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11_8_0 : go 13 7 9 [9, 11, 8, 0] = true := by decide +kernel
theorem m13_9_11_8_1 : go 13 7 9 [9, 11, 8, 1] = true := by decide +kernel
theorem m13_9_11_8_2 : go 13 7 9 [9, 11, 8, 2] = true := by decide +kernel
theorem m13_9_11_8_3 : go 13 7 9 [9, 11, 8, 3] = true := by decide +kernel
theorem m13_9_11_8_4 : go 13 7 9 [9, 11, 8, 4] = true := by decide +kernel
theorem m13_9_11_8_5 : go 13 7 9 [9, 11, 8, 5] = true := by decide +kernel
theorem m13_9_11_8_10 : go 13 7 9 [9, 11, 8, 10] = true := by decide +kernel

theorem m13_9_11_8 : go 13 7 10 [9, 11, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_8_0
  · exact m13_9_11_8_1
  · exact m13_9_11_8_2
  · exact m13_9_11_8_3
  · exact m13_9_11_8_4
  · exact m13_9_11_8_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_9_11_8_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_9_11 : go 13 7 11 [9, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_9_11_0
  · exact m13_9_11_1
  · exact m13_9_11_2
  · exact m13_9_11_3
  · exact m13_9_11_4
  · exact m13_9_11_5
  · exact m13_9_11_6
  · exact absurd hs (by decide)
  · exact m13_9_11_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
