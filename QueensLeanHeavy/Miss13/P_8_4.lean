import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [8, 4]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_8_4_0_3 : go 13 7 9 [8, 4, 0, 3] = true := by decide +kernel
theorem m13_8_4_0_7 : go 13 7 9 [8, 4, 0, 7] = true := by decide +kernel
theorem m13_8_4_0_9 : go 13 7 9 [8, 4, 0, 9] = true := by decide +kernel
theorem m13_8_4_0_10 : go 13 7 9 [8, 4, 0, 10] = true := by decide +kernel
theorem m13_8_4_0_12 : go 13 7 9 [8, 4, 0, 12] = true := by decide +kernel

theorem m13_8_4_0 : go 13 7 10 [8, 4, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_0_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_0_7
  · exact absurd hs (by decide)
  · exact m13_8_4_0_9
  · exact m13_8_4_0_10
  · exact absurd hs (by decide)
  · exact m13_8_4_0_12

theorem m13_8_4_1_3 : go 13 7 9 [8, 4, 1, 3] = true := by decide +kernel
theorem m13_8_4_1_7 : go 13 7 9 [8, 4, 1, 7] = true := by decide +kernel
theorem m13_8_4_1_9 : go 13 7 9 [8, 4, 1, 9] = true := by decide +kernel
theorem m13_8_4_1_10 : go 13 7 9 [8, 4, 1, 10] = true := by decide +kernel
theorem m13_8_4_1_12 : go 13 7 9 [8, 4, 1, 12] = true := by decide +kernel

theorem m13_8_4_1 : go 13 7 10 [8, 4, 1] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_1_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_1_7
  · exact absurd hs (by decide)
  · exact m13_8_4_1_9
  · exact m13_8_4_1_10
  · exact absurd hs (by decide)
  · exact m13_8_4_1_12

theorem m13_8_4_2_0 : go 13 7 9 [8, 4, 2, 0] = true := by decide +kernel
theorem m13_8_4_2_7 : go 13 7 9 [8, 4, 2, 7] = true := by decide +kernel
theorem m13_8_4_2_9 : go 13 7 9 [8, 4, 2, 9] = true := by decide +kernel
theorem m13_8_4_2_10 : go 13 7 9 [8, 4, 2, 10] = true := by decide +kernel
theorem m13_8_4_2_12 : go 13 7 9 [8, 4, 2, 12] = true := by decide +kernel

theorem m13_8_4_2 : go 13 7 10 [8, 4, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_4_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_2_7
  · exact absurd hs (by decide)
  · exact m13_8_4_2_9
  · exact m13_8_4_2_10
  · exact absurd hs (by decide)
  · exact m13_8_4_2_12

theorem m13_8_4_7_0 : go 13 7 9 [8, 4, 7, 0] = true := by decide +kernel
theorem m13_8_4_7_1 : go 13 7 9 [8, 4, 7, 1] = true := by decide +kernel
theorem m13_8_4_7_3 : go 13 7 9 [8, 4, 7, 3] = true := by decide +kernel
theorem m13_8_4_7_9 : go 13 7 9 [8, 4, 7, 9] = true := by decide +kernel
theorem m13_8_4_7_10 : go 13 7 9 [8, 4, 7, 10] = true := by decide +kernel
theorem m13_8_4_7_12 : go 13 7 9 [8, 4, 7, 12] = true := by decide +kernel

theorem m13_8_4_7 : go 13 7 10 [8, 4, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_4_7_0
  · exact m13_8_4_7_1
  · exact absurd hs (by decide)
  · exact m13_8_4_7_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_7_9
  · exact m13_8_4_7_10
  · exact absurd hs (by decide)
  · exact m13_8_4_7_12

theorem m13_8_4_9_0 : go 13 7 9 [8, 4, 9, 0] = true := by decide +kernel
theorem m13_8_4_9_1 : go 13 7 9 [8, 4, 9, 1] = true := by decide +kernel
theorem m13_8_4_9_3 : go 13 7 9 [8, 4, 9, 3] = true := by decide +kernel
theorem m13_8_4_9_7 : go 13 7 9 [8, 4, 9, 7] = true := by decide +kernel
theorem m13_8_4_9_12 : go 13 7 9 [8, 4, 9, 12] = true := by decide +kernel

theorem m13_8_4_9 : go 13 7 10 [8, 4, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_4_9_0
  · exact m13_8_4_9_1
  · exact absurd hs (by decide)
  · exact m13_8_4_9_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_9_7
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_9_12

theorem m13_8_4_11_0 : go 13 7 9 [8, 4, 11, 0] = true := by decide +kernel
theorem m13_8_4_11_1 : go 13 7 9 [8, 4, 11, 1] = true := by decide +kernel
theorem m13_8_4_11_3 : go 13 7 9 [8, 4, 11, 3] = true := by decide +kernel
theorem m13_8_4_11_7 : go 13 7 9 [8, 4, 11, 7] = true := by decide +kernel
theorem m13_8_4_11_9 : go 13 7 9 [8, 4, 11, 9] = true := by decide +kernel

theorem m13_8_4_11 : go 13 7 10 [8, 4, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_4_11_0
  · exact m13_8_4_11_1
  · exact absurd hs (by decide)
  · exact m13_8_4_11_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_11_7
  · exact absurd hs (by decide)
  · exact m13_8_4_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_4_12_0 : go 13 7 9 [8, 4, 12, 0] = true := by decide +kernel
theorem m13_8_4_12_1 : go 13 7 9 [8, 4, 12, 1] = true := by decide +kernel
theorem m13_8_4_12_3 : go 13 7 9 [8, 4, 12, 3] = true := by decide +kernel
theorem m13_8_4_12_7 : go 13 7 9 [8, 4, 12, 7] = true := by decide +kernel
theorem m13_8_4_12_9 : go 13 7 9 [8, 4, 12, 9] = true := by decide +kernel
theorem m13_8_4_12_10 : go 13 7 9 [8, 4, 12, 10] = true := by decide +kernel

theorem m13_8_4_12 : go 13 7 10 [8, 4, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_4_12_0
  · exact m13_8_4_12_1
  · exact absurd hs (by decide)
  · exact m13_8_4_12_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_12_7
  · exact absurd hs (by decide)
  · exact m13_8_4_12_9
  · exact m13_8_4_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_8_4 : go 13 7 11 [8, 4] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_8_4_0
  · exact m13_8_4_1
  · exact m13_8_4_2
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_8_4_7
  · exact absurd hs (by decide)
  · exact m13_8_4_9
  · exact absurd hs (by decide)
  · exact m13_8_4_11
  · exact m13_8_4_12

end Misses
