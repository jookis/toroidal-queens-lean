import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [4, 11]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_4_11_0_2 : go 13 7 9 [4, 11, 0, 2] = true := by decide +kernel
theorem m13_4_11_0_3 : go 13 7 9 [4, 11, 0, 3] = true := by decide +kernel
theorem m13_4_11_0_5 : go 13 7 9 [4, 11, 0, 5] = true := by decide +kernel
theorem m13_4_11_0_6 : go 13 7 9 [4, 11, 0, 6] = true := by decide +kernel
theorem m13_4_11_0_8 : go 13 7 9 [4, 11, 0, 8] = true := by decide +kernel
theorem m13_4_11_0_10 : go 13 7 9 [4, 11, 0, 10] = true := by decide +kernel
theorem m13_4_11_0_12 : go 13 7 9 [4, 11, 0, 12] = true := by decide +kernel

theorem m13_4_11_0 : go 13 7 10 [4, 11, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_0_2
  · exact m13_4_11_0_3
  · exact absurd hs (by decide)
  · exact m13_4_11_0_5
  · exact m13_4_11_0_6
  · exact absurd hs (by decide)
  · exact m13_4_11_0_8
  · exact absurd hs (by decide)
  · exact m13_4_11_0_10
  · exact absurd hs (by decide)
  · exact m13_4_11_0_12

theorem m13_4_11_1_3 : go 13 7 9 [4, 11, 1, 3] = true := by decide +kernel
theorem m13_4_11_1_5 : go 13 7 9 [4, 11, 1, 5] = true := by decide +kernel
theorem m13_4_11_1_6 : go 13 7 9 [4, 11, 1, 6] = true := by decide +kernel
theorem m13_4_11_1_8 : go 13 7 9 [4, 11, 1, 8] = true := by decide +kernel
theorem m13_4_11_1_10 : go 13 7 9 [4, 11, 1, 10] = true := by decide +kernel
theorem m13_4_11_1_12 : go 13 7 9 [4, 11, 1, 12] = true := by decide +kernel

theorem m13_4_11_1 : go 13 7 10 [4, 11, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_1_3
  · exact absurd hs (by decide)
  · exact m13_4_11_1_5
  · exact m13_4_11_1_6
  · exact absurd hs (by decide)
  · exact m13_4_11_1_8
  · exact absurd hs (by decide)
  · exact m13_4_11_1_10
  · exact absurd hs (by decide)
  · exact m13_4_11_1_12

theorem m13_4_11_3_0 : go 13 7 9 [4, 11, 3, 0] = true := by decide +kernel
theorem m13_4_11_3_5 : go 13 7 9 [4, 11, 3, 5] = true := by decide +kernel
theorem m13_4_11_3_6 : go 13 7 9 [4, 11, 3, 6] = true := by decide +kernel
theorem m13_4_11_3_8 : go 13 7 9 [4, 11, 3, 8] = true := by decide +kernel
theorem m13_4_11_3_10 : go 13 7 9 [4, 11, 3, 10] = true := by decide +kernel
theorem m13_4_11_3_12 : go 13 7 9 [4, 11, 3, 12] = true := by decide +kernel

theorem m13_4_11_3 : go 13 7 10 [4, 11, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_11_3_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_3_5
  · exact m13_4_11_3_6
  · exact absurd hs (by decide)
  · exact m13_4_11_3_8
  · exact absurd hs (by decide)
  · exact m13_4_11_3_10
  · exact absurd hs (by decide)
  · exact m13_4_11_3_12

theorem m13_4_11_5_0 : go 13 7 9 [4, 11, 5, 0] = true := by decide +kernel
theorem m13_4_11_5_2 : go 13 7 9 [4, 11, 5, 2] = true := by decide +kernel
theorem m13_4_11_5_3 : go 13 7 9 [4, 11, 5, 3] = true := by decide +kernel
theorem m13_4_11_5_8 : go 13 7 9 [4, 11, 5, 8] = true := by decide +kernel
theorem m13_4_11_5_10 : go 13 7 9 [4, 11, 5, 10] = true := by decide +kernel
theorem m13_4_11_5_12 : go 13 7 9 [4, 11, 5, 12] = true := by decide +kernel

theorem m13_4_11_5 : go 13 7 10 [4, 11, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_11_5_0
  · exact absurd hs (by decide)
  · exact m13_4_11_5_2
  · exact m13_4_11_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_5_8
  · exact absurd hs (by decide)
  · exact m13_4_11_5_10
  · exact absurd hs (by decide)
  · exact m13_4_11_5_12

theorem m13_4_11_7_0 : go 13 7 9 [4, 11, 7, 0] = true := by decide +kernel
theorem m13_4_11_7_2 : go 13 7 9 [4, 11, 7, 2] = true := by decide +kernel
theorem m13_4_11_7_3 : go 13 7 9 [4, 11, 7, 3] = true := by decide +kernel
theorem m13_4_11_7_5 : go 13 7 9 [4, 11, 7, 5] = true := by decide +kernel
theorem m13_4_11_7_10 : go 13 7 9 [4, 11, 7, 10] = true := by decide +kernel
theorem m13_4_11_7_12 : go 13 7 9 [4, 11, 7, 12] = true := by decide +kernel

theorem m13_4_11_7 : go 13 7 10 [4, 11, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_11_7_0
  · exact absurd hs (by decide)
  · exact m13_4_11_7_2
  · exact m13_4_11_7_3
  · exact absurd hs (by decide)
  · exact m13_4_11_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_7_10
  · exact absurd hs (by decide)
  · exact m13_4_11_7_12

theorem m13_4_11_8_0 : go 13 7 9 [4, 11, 8, 0] = true := by decide +kernel
theorem m13_4_11_8_2 : go 13 7 9 [4, 11, 8, 2] = true := by decide +kernel
theorem m13_4_11_8_3 : go 13 7 9 [4, 11, 8, 3] = true := by decide +kernel
theorem m13_4_11_8_5 : go 13 7 9 [4, 11, 8, 5] = true := by decide +kernel
theorem m13_4_11_8_6 : go 13 7 9 [4, 11, 8, 6] = true := by decide +kernel
theorem m13_4_11_8_10 : go 13 7 9 [4, 11, 8, 10] = true := by decide +kernel
theorem m13_4_11_8_12 : go 13 7 9 [4, 11, 8, 12] = true := by decide +kernel

theorem m13_4_11_8 : go 13 7 10 [4, 11, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_11_8_0
  · exact absurd hs (by decide)
  · exact m13_4_11_8_2
  · exact m13_4_11_8_3
  · exact absurd hs (by decide)
  · exact m13_4_11_8_5
  · exact m13_4_11_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_8_10
  · exact absurd hs (by decide)
  · exact m13_4_11_8_12

theorem m13_4_11_9_0 : go 13 7 9 [4, 11, 9, 0] = true := by decide +kernel
theorem m13_4_11_9_2 : go 13 7 9 [4, 11, 9, 2] = true := by decide +kernel
theorem m13_4_11_9_3 : go 13 7 9 [4, 11, 9, 3] = true := by decide +kernel
theorem m13_4_11_9_5 : go 13 7 9 [4, 11, 9, 5] = true := by decide +kernel
theorem m13_4_11_9_6 : go 13 7 9 [4, 11, 9, 6] = true := by decide +kernel
theorem m13_4_11_9_12 : go 13 7 9 [4, 11, 9, 12] = true := by decide +kernel

theorem m13_4_11_9 : go 13 7 10 [4, 11, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_11_9_0
  · exact absurd hs (by decide)
  · exact m13_4_11_9_2
  · exact m13_4_11_9_3
  · exact absurd hs (by decide)
  · exact m13_4_11_9_5
  · exact m13_4_11_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_11_9_12

theorem m13_4_11 : go 13 7 11 [4, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_11_0
  · exact m13_4_11_1
  · exact absurd hs (by decide)
  · exact m13_4_11_3
  · exact absurd hs (by decide)
  · exact m13_4_11_5
  · exact absurd hs (by decide)
  · exact m13_4_11_7
  · exact m13_4_11_8
  · exact m13_4_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

end Misses
