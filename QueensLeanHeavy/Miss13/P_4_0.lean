import QueensLean.Misses

/-! Prefix searches for `C(13)` under the rows [4, 0]. -/

namespace Misses

set_option maxHeartbeats 0
set_option Elab.async false

theorem m13_4_0_3_5 : go 13 7 9 [4, 0, 3, 5] = true := by decide +kernel
theorem m13_4_0_3_6 : go 13 7 9 [4, 0, 3, 6] = true := by decide +kernel
theorem m13_4_0_3_8 : go 13 7 9 [4, 0, 3, 8] = true := by decide +kernel
theorem m13_4_0_3_9 : go 13 7 9 [4, 0, 3, 9] = true := by decide +kernel
theorem m13_4_0_3_10 : go 13 7 9 [4, 0, 3, 10] = true := by decide +kernel
theorem m13_4_0_3_11 : go 13 7 9 [4, 0, 3, 11] = true := by decide +kernel
theorem m13_4_0_3_12 : go 13 7 9 [4, 0, 3, 12] = true := by decide +kernel

theorem m13_4_0_3 : go 13 7 10 [4, 0, 3] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_3_5
  · exact m13_4_0_3_6
  · exact absurd hs (by decide)
  · exact m13_4_0_3_8
  · exact m13_4_0_3_9
  · exact m13_4_0_3_10
  · exact m13_4_0_3_11
  · exact m13_4_0_3_12

theorem m13_4_0_5_3 : go 13 7 9 [4, 0, 5, 3] = true := by decide +kernel
theorem m13_4_0_5_8 : go 13 7 9 [4, 0, 5, 8] = true := by decide +kernel
theorem m13_4_0_5_9 : go 13 7 9 [4, 0, 5, 9] = true := by decide +kernel
theorem m13_4_0_5_10 : go 13 7 9 [4, 0, 5, 10] = true := by decide +kernel
theorem m13_4_0_5_11 : go 13 7 9 [4, 0, 5, 11] = true := by decide +kernel
theorem m13_4_0_5_12 : go 13 7 9 [4, 0, 5, 12] = true := by decide +kernel

theorem m13_4_0_5 : go 13 7 10 [4, 0, 5] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_5_3
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_5_8
  · exact m13_4_0_5_9
  · exact m13_4_0_5_10
  · exact m13_4_0_5_11
  · exact m13_4_0_5_12

theorem m13_4_0_7_3 : go 13 7 9 [4, 0, 7, 3] = true := by decide +kernel
theorem m13_4_0_7_5 : go 13 7 9 [4, 0, 7, 5] = true := by decide +kernel
theorem m13_4_0_7_9 : go 13 7 9 [4, 0, 7, 9] = true := by decide +kernel
theorem m13_4_0_7_10 : go 13 7 9 [4, 0, 7, 10] = true := by decide +kernel
theorem m13_4_0_7_11 : go 13 7 9 [4, 0, 7, 11] = true := by decide +kernel
theorem m13_4_0_7_12 : go 13 7 9 [4, 0, 7, 12] = true := by decide +kernel

theorem m13_4_0_7 : go 13 7 10 [4, 0, 7] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_7_3
  · exact absurd hs (by decide)
  · exact m13_4_0_7_5
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_7_9
  · exact m13_4_0_7_10
  · exact m13_4_0_7_11
  · exact m13_4_0_7_12

theorem m13_4_0_8_3 : go 13 7 9 [4, 0, 8, 3] = true := by decide +kernel
theorem m13_4_0_8_5 : go 13 7 9 [4, 0, 8, 5] = true := by decide +kernel
theorem m13_4_0_8_6 : go 13 7 9 [4, 0, 8, 6] = true := by decide +kernel
theorem m13_4_0_8_10 : go 13 7 9 [4, 0, 8, 10] = true := by decide +kernel
theorem m13_4_0_8_11 : go 13 7 9 [4, 0, 8, 11] = true := by decide +kernel
theorem m13_4_0_8_12 : go 13 7 9 [4, 0, 8, 12] = true := by decide +kernel

theorem m13_4_0_8 : go 13 7 10 [4, 0, 8] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_8_3
  · exact absurd hs (by decide)
  · exact m13_4_0_8_5
  · exact m13_4_0_8_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_8_10
  · exact m13_4_0_8_11
  · exact m13_4_0_8_12

theorem m13_4_0_9_3 : go 13 7 9 [4, 0, 9, 3] = true := by decide +kernel
theorem m13_4_0_9_5 : go 13 7 9 [4, 0, 9, 5] = true := by decide +kernel
theorem m13_4_0_9_6 : go 13 7 9 [4, 0, 9, 6] = true := by decide +kernel
theorem m13_4_0_9_11 : go 13 7 9 [4, 0, 9, 11] = true := by decide +kernel
theorem m13_4_0_9_12 : go 13 7 9 [4, 0, 9, 12] = true := by decide +kernel

theorem m13_4_0_9 : go 13 7 10 [4, 0, 9] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_9_3
  · exact absurd hs (by decide)
  · exact m13_4_0_9_5
  · exact m13_4_0_9_6
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_9_11
  · exact m13_4_0_9_12

theorem m13_4_0_10_3 : go 13 7 9 [4, 0, 10, 3] = true := by decide +kernel
theorem m13_4_0_10_5 : go 13 7 9 [4, 0, 10, 5] = true := by decide +kernel
theorem m13_4_0_10_6 : go 13 7 9 [4, 0, 10, 6] = true := by decide +kernel
theorem m13_4_0_10_8 : go 13 7 9 [4, 0, 10, 8] = true := by decide +kernel
theorem m13_4_0_10_12 : go 13 7 9 [4, 0, 10, 12] = true := by decide +kernel

theorem m13_4_0_10 : go 13 7 10 [4, 0, 10] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_10_3
  · exact absurd hs (by decide)
  · exact m13_4_0_10_5
  · exact m13_4_0_10_6
  · exact absurd hs (by decide)
  · exact m13_4_0_10_8
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_10_12

theorem m13_4_0_11_3 : go 13 7 9 [4, 0, 11, 3] = true := by decide +kernel
theorem m13_4_0_11_5 : go 13 7 9 [4, 0, 11, 5] = true := by decide +kernel
theorem m13_4_0_11_6 : go 13 7 9 [4, 0, 11, 6] = true := by decide +kernel
theorem m13_4_0_11_8 : go 13 7 9 [4, 0, 11, 8] = true := by decide +kernel
theorem m13_4_0_11_9 : go 13 7 9 [4, 0, 11, 9] = true := by decide +kernel

theorem m13_4_0_11 : go 13 7 10 [4, 0, 11] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_11_3
  · exact absurd hs (by decide)
  · exact m13_4_0_11_5
  · exact m13_4_0_11_6
  · exact absurd hs (by decide)
  · exact m13_4_0_11_8
  · exact m13_4_0_11_9
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_0_12_3 : go 13 7 9 [4, 0, 12, 3] = true := by decide +kernel
theorem m13_4_0_12_5 : go 13 7 9 [4, 0, 12, 5] = true := by decide +kernel
theorem m13_4_0_12_6 : go 13 7 9 [4, 0, 12, 6] = true := by decide +kernel
theorem m13_4_0_12_8 : go 13 7 9 [4, 0, 12, 8] = true := by decide +kernel
theorem m13_4_0_12_9 : go 13 7 9 [4, 0, 12, 9] = true := by decide +kernel
theorem m13_4_0_12_10 : go 13 7 9 [4, 0, 12, 10] = true := by decide +kernel

theorem m13_4_0_12 : go 13 7 10 [4, 0, 12] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_12_3
  · exact absurd hs (by decide)
  · exact m13_4_0_12_5
  · exact m13_4_0_12_6
  · exact absurd hs (by decide)
  · exact m13_4_0_12_8
  · exact m13_4_0_12_9
  · exact m13_4_0_12_10
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)

theorem m13_4_0 : go 13 7 11 [4, 0] = true := go_of fun c hc hs => by
  interval_cases c
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact absurd hs (by decide)
  · exact m13_4_0_3
  · exact absurd hs (by decide)
  · exact m13_4_0_5
  · exact absurd hs (by decide)
  · exact m13_4_0_7
  · exact m13_4_0_8
  · exact m13_4_0_9
  · exact m13_4_0_10
  · exact m13_4_0_11
  · exact m13_4_0_12

end Misses
