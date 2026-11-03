import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [5, 11]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_5_11_0_3 : go 13 7 9 [5, 11, 0, 3] = true := by decide +kernel
theorem m13_5_11_0_4 : go 13 7 9 [5, 11, 0, 4] = true := by decide +kernel
theorem m13_5_11_0_6 : go 13 7 9 [5, 11, 0, 6] = true := by decide +kernel
theorem m13_5_11_0_7 : go 13 7 9 [5, 11, 0, 7] = true := by decide +kernel
theorem m13_5_11_0_10 : go 13 7 9 [5, 11, 0, 10] = true := by decide +kernel
theorem m13_5_11_0_12 : go 13 7 9 [5, 11, 0, 12] = true := by decide +kernel

theorem m13_5_11_0 : go 13 7 10 [5, 11, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_0_3
  · exact m13_5_11_0_4
  · exact absurd hs (by decide)
  · exact m13_5_11_0_6
  · exact m13_5_11_0_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_0_10
  · exact absurd hs (by decide)
  · exact m13_5_11_0_12

theorem m13_5_11_1_3 : go 13 7 9 [5, 11, 1, 3] = true := by decide +kernel
theorem m13_5_11_1_4 : go 13 7 9 [5, 11, 1, 4] = true := by decide +kernel
theorem m13_5_11_1_6 : go 13 7 9 [5, 11, 1, 6] = true := by decide +kernel
theorem m13_5_11_1_7 : go 13 7 9 [5, 11, 1, 7] = true := by decide +kernel
theorem m13_5_11_1_10 : go 13 7 9 [5, 11, 1, 10] = true := by decide +kernel
theorem m13_5_11_1_12 : go 13 7 9 [5, 11, 1, 12] = true := by decide +kernel

theorem m13_5_11_1 : go 13 7 10 [5, 11, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_1_3
  · exact m13_5_11_1_4
  · exact absurd hs (by decide)
  · exact m13_5_11_1_6
  · exact m13_5_11_1_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_1_10
  · exact absurd hs (by decide)
  · exact m13_5_11_1_12

theorem m13_5_11_2_0 : go 13 7 9 [5, 11, 2, 0] = true := by decide +kernel
theorem m13_5_11_2_4 : go 13 7 9 [5, 11, 2, 4] = true := by decide +kernel
theorem m13_5_11_2_6 : go 13 7 9 [5, 11, 2, 6] = true := by decide +kernel
theorem m13_5_11_2_7 : go 13 7 9 [5, 11, 2, 7] = true := by decide +kernel
theorem m13_5_11_2_10 : go 13 7 9 [5, 11, 2, 10] = true := by decide +kernel
theorem m13_5_11_2_12 : go 13 7 9 [5, 11, 2, 12] = true := by decide +kernel

theorem m13_5_11_2 : go 13 7 10 [5, 11, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_11_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_2_4
  · exact absurd hs (by decide)
  · exact m13_5_11_2_6
  · exact m13_5_11_2_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_2_10
  · exact absurd hs (by decide)
  · exact m13_5_11_2_12

theorem m13_5_11_4_0 : go 13 7 9 [5, 11, 4, 0] = true := by decide +kernel
theorem m13_5_11_4_1 : go 13 7 9 [5, 11, 4, 1] = true := by decide +kernel
theorem m13_5_11_4_6 : go 13 7 9 [5, 11, 4, 6] = true := by decide +kernel
theorem m13_5_11_4_7 : go 13 7 9 [5, 11, 4, 7] = true := by decide +kernel
theorem m13_5_11_4_10 : go 13 7 9 [5, 11, 4, 10] = true := by decide +kernel
theorem m13_5_11_4_12 : go 13 7 9 [5, 11, 4, 12] = true := by decide +kernel

theorem m13_5_11_4 : go 13 7 10 [5, 11, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_11_4_0
  · exact m13_5_11_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_4_6
  · exact m13_5_11_4_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_4_10
  · exact absurd hs (by decide)
  · exact m13_5_11_4_12

theorem m13_5_11_6_0 : go 13 7 9 [5, 11, 6, 0] = true := by decide +kernel
theorem m13_5_11_6_1 : go 13 7 9 [5, 11, 6, 1] = true := by decide +kernel
theorem m13_5_11_6_3 : go 13 7 9 [5, 11, 6, 3] = true := by decide +kernel
theorem m13_5_11_6_4 : go 13 7 9 [5, 11, 6, 4] = true := by decide +kernel
theorem m13_5_11_6_10 : go 13 7 9 [5, 11, 6, 10] = true := by decide +kernel
theorem m13_5_11_6_12 : go 13 7 9 [5, 11, 6, 12] = true := by decide +kernel

theorem m13_5_11_6 : go 13 7 10 [5, 11, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_11_6_0
  · exact m13_5_11_6_1
  · exact absurd hs (by decide)
  · exact m13_5_11_6_3
  · exact m13_5_11_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_6_10
  · exact absurd hs (by decide)
  · exact m13_5_11_6_12

theorem m13_5_11_8_0 : go 13 7 9 [5, 11, 8, 0] = true := by decide +kernel
theorem m13_5_11_8_1 : go 13 7 9 [5, 11, 8, 1] = true := by decide +kernel
theorem m13_5_11_8_3 : go 13 7 9 [5, 11, 8, 3] = true := by decide +kernel
theorem m13_5_11_8_4 : go 13 7 9 [5, 11, 8, 4] = true := by decide +kernel
theorem m13_5_11_8_6 : go 13 7 9 [5, 11, 8, 6] = true := by decide +kernel
theorem m13_5_11_8_10 : go 13 7 9 [5, 11, 8, 10] = true := by decide +kernel
theorem m13_5_11_8_12 : go 13 7 9 [5, 11, 8, 12] = true := by decide +kernel

theorem m13_5_11_8 : go 13 7 10 [5, 11, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_11_8_0
  · exact m13_5_11_8_1
  · exact absurd hs (by decide)
  · exact m13_5_11_8_3
  · exact m13_5_11_8_4
  · exact absurd hs (by decide)
  · exact m13_5_11_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_8_10
  · exact absurd hs (by decide)
  · exact m13_5_11_8_12

theorem m13_5_11_9_0 : go 13 7 9 [5, 11, 9, 0] = true := by decide +kernel
theorem m13_5_11_9_1 : go 13 7 9 [5, 11, 9, 1] = true := by decide +kernel
theorem m13_5_11_9_3 : go 13 7 9 [5, 11, 9, 3] = true := by decide +kernel
theorem m13_5_11_9_4 : go 13 7 9 [5, 11, 9, 4] = true := by decide +kernel
theorem m13_5_11_9_6 : go 13 7 9 [5, 11, 9, 6] = true := by decide +kernel
theorem m13_5_11_9_7 : go 13 7 9 [5, 11, 9, 7] = true := by decide +kernel
theorem m13_5_11_9_12 : go 13 7 9 [5, 11, 9, 12] = true := by decide +kernel

theorem m13_5_11_9 : go 13 7 10 [5, 11, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_11_9_0
  · exact m13_5_11_9_1
  · exact absurd hs (by decide)
  · exact m13_5_11_9_3
  · exact m13_5_11_9_4
  · exact absurd hs (by decide)
  · exact m13_5_11_9_6
  · exact m13_5_11_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_5_11_9_12

theorem m13_5_11 : go 13 7 11 [5, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_5_11_0
  · exact m13_5_11_1
  · exact m13_5_11_2
  · exact absurd hs (by decide)
  · exact m13_5_11_4
  · exact absurd hs (by decide)
  · exact m13_5_11_6
  · exact absurd hs (by decide)
  · exact m13_5_11_8
  · exact m13_5_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
