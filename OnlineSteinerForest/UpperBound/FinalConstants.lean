import OnlineSteinerForest.UpperBound.FinalParameters

/-! Absolute positive constants used to convert discrete accounting factors to natural logs. -/
namespace OnlineSteinerForest.UpperBound

noncomputable def pairLogConstant : ℝ := 5 / Real.log 2
noncomputable def iteratedLogFloor : ℝ := Real.log (Real.log 4)
noncomputable def classLogConstant : ℝ :=
  (29 + 5 * Real.log pairLogConstant / Real.log 2) / iteratedLogFloor + 5 / Real.log 2
noncomputable def cycleLogConstant : ℝ :=
  (5 + Real.log pairLogConstant / Real.log 2) / iteratedLogFloor + 1 / Real.log 2

theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  rw [Real.log_inv] at h
  norm_num at h
  linarith

theorem pairLogConstant_gt_one : 1 < pairLogConstant := by
  unfold pairLogConstant
  apply (lt_div_iff₀ log_two_pos).mpr
  have hh := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
  linarith

theorem pairLogConstant_pos : 0 < pairLogConstant := lt_trans zero_lt_one pairLogConstant_gt_one

theorem log_pairLogConstant_pos : 0 < Real.log pairLogConstant :=
  Real.log_pos pairLogConstant_gt_one

theorem iteratedLogFloor_pos : 0 < iteratedLogFloor := by
  apply Real.log_pos
  have hh : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [hh]
  linarith [half_lt_log_two]

theorem classLogConstant_pos : 0 < classLogConstant := by
  unfold classLogConstant
  have ha := log_two_pos
  have hb := iteratedLogFloor_pos
  have hc := log_pairLogConstant_pos
  positivity

theorem cycleLogConstant_pos : 0 < cycleLogConstant := by
  unfold cycleLogConstant
  have ha := log_two_pos
  have hb := iteratedLogFloor_pos
  have hc := log_pairLogConstant_pos
  positivity

end OnlineSteinerForest.UpperBound
