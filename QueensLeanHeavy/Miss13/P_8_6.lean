import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [8, 6]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_8_6_0_2 : go 13 7 9 [8, 6, 0, 2] = true := by decide +kernel
theorem m13_8_6_0_3 : go 13 7 9 [8, 6, 0, 3] = true := by decide +kernel
theorem m13_8_6_0_7 : go 13 7 9 [8, 6, 0, 7] = true := by decide +kernel
theorem m13_8_6_0_9 : go 13 7 9 [8, 6, 0, 9] = true := by decide +kernel
theorem m13_8_6_0_10 : go 13 7 9 [8, 6, 0, 10] = true := by decide +kernel
theorem m13_8_6_0_12 : go 13 7 9 [8, 6, 0, 12] = true := by decide +kernel

theorem m13_8_6_0 : go 13 7 10 [8, 6, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_0_2
  · exact m13_8_6_0_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_0_7
  · exact absurd hs (by decide)
  · exact m13_8_6_0_9
  · exact m13_8_6_0_10
  · exact absurd hs (by decide)
  · exact m13_8_6_0_12

theorem m13_8_6_1_3 : go 13 7 9 [8, 6, 1, 3] = true := by decide +kernel
theorem m13_8_6_1_7 : go 13 7 9 [8, 6, 1, 7] = true := by decide +kernel
theorem m13_8_6_1_9 : go 13 7 9 [8, 6, 1, 9] = true := by decide +kernel
theorem m13_8_6_1_10 : go 13 7 9 [8, 6, 1, 10] = true := by decide +kernel
theorem m13_8_6_1_12 : go 13 7 9 [8, 6, 1, 12] = true := by decide +kernel

theorem m13_8_6_1 : go 13 7 10 [8, 6, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_1_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_1_7
  · exact absurd hs (by decide)
  · exact m13_8_6_1_9
  · exact m13_8_6_1_10
  · exact absurd hs (by decide)
  · exact m13_8_6_1_12

theorem m13_8_6_2_0 : go 13 7 9 [8, 6, 2, 0] = true := by decide +kernel
theorem m13_8_6_2_7 : go 13 7 9 [8, 6, 2, 7] = true := by decide +kernel
theorem m13_8_6_2_9 : go 13 7 9 [8, 6, 2, 9] = true := by decide +kernel
theorem m13_8_6_2_10 : go 13 7 9 [8, 6, 2, 10] = true := by decide +kernel
theorem m13_8_6_2_12 : go 13 7 9 [8, 6, 2, 12] = true := by decide +kernel

theorem m13_8_6_2 : go 13 7 10 [8, 6, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_2_7
  · exact absurd hs (by decide)
  · exact m13_8_6_2_9
  · exact m13_8_6_2_10
  · exact absurd hs (by decide)
  · exact m13_8_6_2_12

theorem m13_8_6_3_0 : go 13 7 9 [8, 6, 3, 0] = true := by decide +kernel
theorem m13_8_6_3_1 : go 13 7 9 [8, 6, 3, 1] = true := by decide +kernel
theorem m13_8_6_3_7 : go 13 7 9 [8, 6, 3, 7] = true := by decide +kernel
theorem m13_8_6_3_9 : go 13 7 9 [8, 6, 3, 9] = true := by decide +kernel
theorem m13_8_6_3_10 : go 13 7 9 [8, 6, 3, 10] = true := by decide +kernel
theorem m13_8_6_3_12 : go 13 7 9 [8, 6, 3, 12] = true := by decide +kernel

theorem m13_8_6_3 : go 13 7 10 [8, 6, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_3_0
  · exact m13_8_6_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_3_7
  · exact absurd hs (by decide)
  · exact m13_8_6_3_9
  · exact m13_8_6_3_10
  · exact absurd hs (by decide)
  · exact m13_8_6_3_12

theorem m13_8_6_4_0 : go 13 7 9 [8, 6, 4, 0] = true := by decide +kernel
theorem m13_8_6_4_1 : go 13 7 9 [8, 6, 4, 1] = true := by decide +kernel
theorem m13_8_6_4_2 : go 13 7 9 [8, 6, 4, 2] = true := by decide +kernel
theorem m13_8_6_4_7 : go 13 7 9 [8, 6, 4, 7] = true := by decide +kernel
theorem m13_8_6_4_9 : go 13 7 9 [8, 6, 4, 9] = true := by decide +kernel
theorem m13_8_6_4_10 : go 13 7 9 [8, 6, 4, 10] = true := by decide +kernel
theorem m13_8_6_4_12 : go 13 7 9 [8, 6, 4, 12] = true := by decide +kernel

theorem m13_8_6_4 : go 13 7 10 [8, 6, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_4_0
  · exact m13_8_6_4_1
  · exact m13_8_6_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_4_7
  · exact absurd hs (by decide)
  · exact m13_8_6_4_9
  · exact m13_8_6_4_10
  · exact absurd hs (by decide)
  · exact m13_8_6_4_12

theorem m13_8_6_9_0 : go 13 7 9 [8, 6, 9, 0] = true := by decide +kernel
theorem m13_8_6_9_1 : go 13 7 9 [8, 6, 9, 1] = true := by decide +kernel
theorem m13_8_6_9_2 : go 13 7 9 [8, 6, 9, 2] = true := by decide +kernel
theorem m13_8_6_9_3 : go 13 7 9 [8, 6, 9, 3] = true := by decide +kernel
theorem m13_8_6_9_7 : go 13 7 9 [8, 6, 9, 7] = true := by decide +kernel
theorem m13_8_6_9_12 : go 13 7 9 [8, 6, 9, 12] = true := by decide +kernel

theorem m13_8_6_9 : go 13 7 10 [8, 6, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_9_0
  · exact m13_8_6_9_1
  · exact m13_8_6_9_2
  · exact m13_8_6_9_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_9_12

theorem m13_8_6_11_0 : go 13 7 9 [8, 6, 11, 0] = true := by decide +kernel
theorem m13_8_6_11_1 : go 13 7 9 [8, 6, 11, 1] = true := by decide +kernel
theorem m13_8_6_11_2 : go 13 7 9 [8, 6, 11, 2] = true := by decide +kernel
theorem m13_8_6_11_3 : go 13 7 9 [8, 6, 11, 3] = true := by decide +kernel
theorem m13_8_6_11_7 : go 13 7 9 [8, 6, 11, 7] = true := by decide +kernel
theorem m13_8_6_11_9 : go 13 7 9 [8, 6, 11, 9] = true := by decide +kernel

theorem m13_8_6_11 : go 13 7 10 [8, 6, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_11_0
  · exact m13_8_6_11_1
  · exact m13_8_6_11_2
  · exact m13_8_6_11_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_11_7
  · exact absurd hs (by decide)
  · exact m13_8_6_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_6_12_0 : go 13 7 9 [8, 6, 12, 0] = true := by decide +kernel
theorem m13_8_6_12_1 : go 13 7 9 [8, 6, 12, 1] = true := by decide +kernel
theorem m13_8_6_12_2 : go 13 7 9 [8, 6, 12, 2] = true := by decide +kernel
theorem m13_8_6_12_3 : go 13 7 9 [8, 6, 12, 3] = true := by decide +kernel
theorem m13_8_6_12_7 : go 13 7 9 [8, 6, 12, 7] = true := by decide +kernel
theorem m13_8_6_12_9 : go 13 7 9 [8, 6, 12, 9] = true := by decide +kernel
theorem m13_8_6_12_10 : go 13 7 9 [8, 6, 12, 10] = true := by decide +kernel

theorem m13_8_6_12 : go 13 7 10 [8, 6, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_12_0
  · exact m13_8_6_12_1
  · exact m13_8_6_12_2
  · exact m13_8_6_12_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_12_7
  · exact absurd hs (by decide)
  · exact m13_8_6_12_9
  · exact m13_8_6_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_6 : go 13 7 11 [8, 6] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_6_0
  · exact m13_8_6_1
  · exact m13_8_6_2
  · exact m13_8_6_3
  · exact m13_8_6_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_6_9
  · exact absurd hs (by decide)
  · exact m13_8_6_11
  · exact m13_8_6_12

end Misses
