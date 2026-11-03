import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [4, 2]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_4_2_0_3 : go 13 7 9 [4, 2, 0, 3] = true := by decide +kernel
theorem m13_4_2_0_5 : go 13 7 9 [4, 2, 0, 5] = true := by decide +kernel
theorem m13_4_2_0_6 : go 13 7 9 [4, 2, 0, 6] = true := by decide +kernel
theorem m13_4_2_0_8 : go 13 7 9 [4, 2, 0, 8] = true := by decide +kernel
theorem m13_4_2_0_9 : go 13 7 9 [4, 2, 0, 9] = true := by decide +kernel
theorem m13_4_2_0_10 : go 13 7 9 [4, 2, 0, 10] = true := by decide +kernel
theorem m13_4_2_0_11 : go 13 7 9 [4, 2, 0, 11] = true := by decide +kernel
theorem m13_4_2_0_12 : go 13 7 9 [4, 2, 0, 12] = true := by decide +kernel

theorem m13_4_2_0 : go 13 7 10 [4, 2, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_0_3
  · exact absurd hs (by decide)
  · exact m13_4_2_0_5
  · exact m13_4_2_0_6
  · exact absurd hs (by decide)
  · exact m13_4_2_0_8
  · exact m13_4_2_0_9
  · exact m13_4_2_0_10
  · exact m13_4_2_0_11
  · exact m13_4_2_0_12

theorem m13_4_2_5_3 : go 13 7 9 [4, 2, 5, 3] = true := by decide +kernel
theorem m13_4_2_5_8 : go 13 7 9 [4, 2, 5, 8] = true := by decide +kernel
theorem m13_4_2_5_9 : go 13 7 9 [4, 2, 5, 9] = true := by decide +kernel
theorem m13_4_2_5_10 : go 13 7 9 [4, 2, 5, 10] = true := by decide +kernel
theorem m13_4_2_5_11 : go 13 7 9 [4, 2, 5, 11] = true := by decide +kernel
theorem m13_4_2_5_12 : go 13 7 9 [4, 2, 5, 12] = true := by decide +kernel

theorem m13_4_2_5 : go 13 7 10 [4, 2, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_5_8
  · exact m13_4_2_5_9
  · exact m13_4_2_5_10
  · exact m13_4_2_5_11
  · exact m13_4_2_5_12

theorem m13_4_2_7_3 : go 13 7 9 [4, 2, 7, 3] = true := by decide +kernel
theorem m13_4_2_7_5 : go 13 7 9 [4, 2, 7, 5] = true := by decide +kernel
theorem m13_4_2_7_9 : go 13 7 9 [4, 2, 7, 9] = true := by decide +kernel
theorem m13_4_2_7_10 : go 13 7 9 [4, 2, 7, 10] = true := by decide +kernel
theorem m13_4_2_7_11 : go 13 7 9 [4, 2, 7, 11] = true := by decide +kernel
theorem m13_4_2_7_12 : go 13 7 9 [4, 2, 7, 12] = true := by decide +kernel

theorem m13_4_2_7 : go 13 7 10 [4, 2, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_7_3
  · exact absurd hs (by decide)
  · exact m13_4_2_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_7_9
  · exact m13_4_2_7_10
  · exact m13_4_2_7_11
  · exact m13_4_2_7_12

theorem m13_4_2_8_3 : go 13 7 9 [4, 2, 8, 3] = true := by decide +kernel
theorem m13_4_2_8_5 : go 13 7 9 [4, 2, 8, 5] = true := by decide +kernel
theorem m13_4_2_8_6 : go 13 7 9 [4, 2, 8, 6] = true := by decide +kernel
theorem m13_4_2_8_10 : go 13 7 9 [4, 2, 8, 10] = true := by decide +kernel
theorem m13_4_2_8_11 : go 13 7 9 [4, 2, 8, 11] = true := by decide +kernel
theorem m13_4_2_8_12 : go 13 7 9 [4, 2, 8, 12] = true := by decide +kernel

theorem m13_4_2_8 : go 13 7 10 [4, 2, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_8_3
  · exact absurd hs (by decide)
  · exact m13_4_2_8_5
  · exact m13_4_2_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_8_10
  · exact m13_4_2_8_11
  · exact m13_4_2_8_12

theorem m13_4_2_9_3 : go 13 7 9 [4, 2, 9, 3] = true := by decide +kernel
theorem m13_4_2_9_5 : go 13 7 9 [4, 2, 9, 5] = true := by decide +kernel
theorem m13_4_2_9_6 : go 13 7 9 [4, 2, 9, 6] = true := by decide +kernel
theorem m13_4_2_9_11 : go 13 7 9 [4, 2, 9, 11] = true := by decide +kernel
theorem m13_4_2_9_12 : go 13 7 9 [4, 2, 9, 12] = true := by decide +kernel

theorem m13_4_2_9 : go 13 7 10 [4, 2, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_9_3
  · exact absurd hs (by decide)
  · exact m13_4_2_9_5
  · exact m13_4_2_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_9_11
  · exact m13_4_2_9_12

theorem m13_4_2_10_3 : go 13 7 9 [4, 2, 10, 3] = true := by decide +kernel
theorem m13_4_2_10_5 : go 13 7 9 [4, 2, 10, 5] = true := by decide +kernel
theorem m13_4_2_10_6 : go 13 7 9 [4, 2, 10, 6] = true := by decide +kernel
theorem m13_4_2_10_8 : go 13 7 9 [4, 2, 10, 8] = true := by decide +kernel
theorem m13_4_2_10_12 : go 13 7 9 [4, 2, 10, 12] = true := by decide +kernel

theorem m13_4_2_10 : go 13 7 10 [4, 2, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_10_3
  · exact absurd hs (by decide)
  · exact m13_4_2_10_5
  · exact m13_4_2_10_6
  · exact absurd hs (by decide)
  · exact m13_4_2_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_10_12

theorem m13_4_2_11_3 : go 13 7 9 [4, 2, 11, 3] = true := by decide +kernel
theorem m13_4_2_11_5 : go 13 7 9 [4, 2, 11, 5] = true := by decide +kernel
theorem m13_4_2_11_6 : go 13 7 9 [4, 2, 11, 6] = true := by decide +kernel
theorem m13_4_2_11_8 : go 13 7 9 [4, 2, 11, 8] = true := by decide +kernel
theorem m13_4_2_11_9 : go 13 7 9 [4, 2, 11, 9] = true := by decide +kernel

theorem m13_4_2_11 : go 13 7 10 [4, 2, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_11_3
  · exact absurd hs (by decide)
  · exact m13_4_2_11_5
  · exact m13_4_2_11_6
  · exact absurd hs (by decide)
  · exact m13_4_2_11_8
  · exact m13_4_2_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_2_12_3 : go 13 7 9 [4, 2, 12, 3] = true := by decide +kernel
theorem m13_4_2_12_5 : go 13 7 9 [4, 2, 12, 5] = true := by decide +kernel
theorem m13_4_2_12_6 : go 13 7 9 [4, 2, 12, 6] = true := by decide +kernel
theorem m13_4_2_12_8 : go 13 7 9 [4, 2, 12, 8] = true := by decide +kernel
theorem m13_4_2_12_9 : go 13 7 9 [4, 2, 12, 9] = true := by decide +kernel
theorem m13_4_2_12_10 : go 13 7 9 [4, 2, 12, 10] = true := by decide +kernel

theorem m13_4_2_12 : go 13 7 10 [4, 2, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_12_3
  · exact absurd hs (by decide)
  · exact m13_4_2_12_5
  · exact m13_4_2_12_6
  · exact absurd hs (by decide)
  · exact m13_4_2_12_8
  · exact m13_4_2_12_9
  · exact m13_4_2_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_2 : go 13 7 11 [4, 2] = true := go_of fun c hc hs => by
  interval_cases c
  · exact m13_4_2_0
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_2_5
  · exact absurd hs (by decide)
  · exact m13_4_2_7
  · exact m13_4_2_8
  · exact m13_4_2_9
  · exact m13_4_2_10
  · exact m13_4_2_11
  · exact m13_4_2_12

end Misses
