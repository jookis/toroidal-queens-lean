import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [8, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_8_0_2_4 : go 13 7 9 [8, 0, 2, 4] = true := by decide +kernel
theorem m13_8_0_2_6 : go 13 7 9 [8, 0, 2, 6] = true := by decide +kernel
theorem m13_8_0_2_7 : go 13 7 9 [8, 0, 2, 7] = true := by decide +kernel
theorem m13_8_0_2_9 : go 13 7 9 [8, 0, 2, 9] = true := by decide +kernel
theorem m13_8_0_2_10 : go 13 7 9 [8, 0, 2, 10] = true := by decide +kernel
theorem m13_8_0_2_12 : go 13 7 9 [8, 0, 2, 12] = true := by decide +kernel

theorem m13_8_0_2 : go 13 7 10 [8, 0, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_2_4
  · exact absurd hs (by decide)
  · exact m13_8_0_2_6
  · exact m13_8_0_2_7
  · exact absurd hs (by decide)
  · exact m13_8_0_2_9
  · exact m13_8_0_2_10
  · exact absurd hs (by decide)
  · exact m13_8_0_2_12

theorem m13_8_0_3_1 : go 13 7 9 [8, 0, 3, 1] = true := by decide +kernel
theorem m13_8_0_3_6 : go 13 7 9 [8, 0, 3, 6] = true := by decide +kernel
theorem m13_8_0_3_7 : go 13 7 9 [8, 0, 3, 7] = true := by decide +kernel
theorem m13_8_0_3_9 : go 13 7 9 [8, 0, 3, 9] = true := by decide +kernel
theorem m13_8_0_3_10 : go 13 7 9 [8, 0, 3, 10] = true := by decide +kernel
theorem m13_8_0_3_12 : go 13 7 9 [8, 0, 3, 12] = true := by decide +kernel

theorem m13_8_0_3 : go 13 7 10 [8, 0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_3_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_3_6
  · exact m13_8_0_3_7
  · exact absurd hs (by decide)
  · exact m13_8_0_3_9
  · exact m13_8_0_3_10
  · exact absurd hs (by decide)
  · exact m13_8_0_3_12

theorem m13_8_0_4_1 : go 13 7 9 [8, 0, 4, 1] = true := by decide +kernel
theorem m13_8_0_4_6 : go 13 7 9 [8, 0, 4, 6] = true := by decide +kernel
theorem m13_8_0_4_7 : go 13 7 9 [8, 0, 4, 7] = true := by decide +kernel
theorem m13_8_0_4_9 : go 13 7 9 [8, 0, 4, 9] = true := by decide +kernel
theorem m13_8_0_4_10 : go 13 7 9 [8, 0, 4, 10] = true := by decide +kernel
theorem m13_8_0_4_12 : go 13 7 9 [8, 0, 4, 12] = true := by decide +kernel

theorem m13_8_0_4 : go 13 7 10 [8, 0, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_4_1
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_4_6
  · exact m13_8_0_4_7
  · exact absurd hs (by decide)
  · exact m13_8_0_4_9
  · exact m13_8_0_4_10
  · exact absurd hs (by decide)
  · exact m13_8_0_4_12

theorem m13_8_0_5_1 : go 13 7 9 [8, 0, 5, 1] = true := by decide +kernel
theorem m13_8_0_5_3 : go 13 7 9 [8, 0, 5, 3] = true := by decide +kernel
theorem m13_8_0_5_7 : go 13 7 9 [8, 0, 5, 7] = true := by decide +kernel
theorem m13_8_0_5_9 : go 13 7 9 [8, 0, 5, 9] = true := by decide +kernel
theorem m13_8_0_5_10 : go 13 7 9 [8, 0, 5, 10] = true := by decide +kernel
theorem m13_8_0_5_12 : go 13 7 9 [8, 0, 5, 12] = true := by decide +kernel

theorem m13_8_0_5 : go 13 7 10 [8, 0, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_5_1
  · exact absurd hs (by decide)
  · exact m13_8_0_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_5_7
  · exact absurd hs (by decide)
  · exact m13_8_0_5_9
  · exact m13_8_0_5_10
  · exact absurd hs (by decide)
  · exact m13_8_0_5_12

theorem m13_8_0_7_1 : go 13 7 9 [8, 0, 7, 1] = true := by decide +kernel
theorem m13_8_0_7_3 : go 13 7 9 [8, 0, 7, 3] = true := by decide +kernel
theorem m13_8_0_7_4 : go 13 7 9 [8, 0, 7, 4] = true := by decide +kernel
theorem m13_8_0_7_9 : go 13 7 9 [8, 0, 7, 9] = true := by decide +kernel
theorem m13_8_0_7_10 : go 13 7 9 [8, 0, 7, 10] = true := by decide +kernel
theorem m13_8_0_7_12 : go 13 7 9 [8, 0, 7, 12] = true := by decide +kernel

theorem m13_8_0_7 : go 13 7 10 [8, 0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_7_1
  · exact absurd hs (by decide)
  · exact m13_8_0_7_3
  · exact m13_8_0_7_4
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_7_9
  · exact m13_8_0_7_10
  · exact absurd hs (by decide)
  · exact m13_8_0_7_12

theorem m13_8_0_9_1 : go 13 7 9 [8, 0, 9, 1] = true := by decide +kernel
theorem m13_8_0_9_3 : go 13 7 9 [8, 0, 9, 3] = true := by decide +kernel
theorem m13_8_0_9_4 : go 13 7 9 [8, 0, 9, 4] = true := by decide +kernel
theorem m13_8_0_9_6 : go 13 7 9 [8, 0, 9, 6] = true := by decide +kernel
theorem m13_8_0_9_7 : go 13 7 9 [8, 0, 9, 7] = true := by decide +kernel
theorem m13_8_0_9_12 : go 13 7 9 [8, 0, 9, 12] = true := by decide +kernel

theorem m13_8_0_9 : go 13 7 10 [8, 0, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_9_1
  · exact absurd hs (by decide)
  · exact m13_8_0_9_3
  · exact m13_8_0_9_4
  · exact absurd hs (by decide)
  · exact m13_8_0_9_6
  · exact m13_8_0_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_9_12

theorem m13_8_0_11_1 : go 13 7 9 [8, 0, 11, 1] = true := by decide +kernel
theorem m13_8_0_11_3 : go 13 7 9 [8, 0, 11, 3] = true := by decide +kernel
theorem m13_8_0_11_4 : go 13 7 9 [8, 0, 11, 4] = true := by decide +kernel
theorem m13_8_0_11_6 : go 13 7 9 [8, 0, 11, 6] = true := by decide +kernel
theorem m13_8_0_11_7 : go 13 7 9 [8, 0, 11, 7] = true := by decide +kernel
theorem m13_8_0_11_9 : go 13 7 9 [8, 0, 11, 9] = true := by decide +kernel

theorem m13_8_0_11 : go 13 7 10 [8, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_11_1
  · exact absurd hs (by decide)
  · exact m13_8_0_11_3
  · exact m13_8_0_11_4
  · exact absurd hs (by decide)
  · exact m13_8_0_11_6
  · exact m13_8_0_11_7
  · exact absurd hs (by decide)
  · exact m13_8_0_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_0_12_1 : go 13 7 9 [8, 0, 12, 1] = true := by decide +kernel
theorem m13_8_0_12_3 : go 13 7 9 [8, 0, 12, 3] = true := by decide +kernel
theorem m13_8_0_12_4 : go 13 7 9 [8, 0, 12, 4] = true := by decide +kernel
theorem m13_8_0_12_6 : go 13 7 9 [8, 0, 12, 6] = true := by decide +kernel
theorem m13_8_0_12_7 : go 13 7 9 [8, 0, 12, 7] = true := by decide +kernel
theorem m13_8_0_12_9 : go 13 7 9 [8, 0, 12, 9] = true := by decide +kernel
theorem m13_8_0_12_10 : go 13 7 9 [8, 0, 12, 10] = true := by decide +kernel

theorem m13_8_0_12 : go 13 7 10 [8, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact m13_8_0_12_1
  · exact absurd hs (by decide)
  · exact m13_8_0_12_3
  · exact m13_8_0_12_4
  · exact absurd hs (by decide)
  · exact m13_8_0_12_6
  · exact m13_8_0_12_7
  · exact absurd hs (by decide)
  · exact m13_8_0_12_9
  · exact m13_8_0_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_0 : go 13 7 11 [8, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_0_2
  · exact m13_8_0_3
  · exact m13_8_0_4
  · exact m13_8_0_5
  · exact absurd hs (by decide)
  · exact m13_8_0_7
  · exact absurd hs (by decide)
  · exact m13_8_0_9
  · exact absurd hs (by decide)
  · exact m13_8_0_11
  · exact m13_8_0_12

end Misses
