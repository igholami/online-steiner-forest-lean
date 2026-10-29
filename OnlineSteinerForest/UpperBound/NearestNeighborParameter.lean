import OnlineSteinerForest.UpperBound.FinalParameters

/-! The manuscript pair parameter bounds the logarithm of any label-batch size. -/
namespace OnlineSteinerForest.UpperBound

theorem log_card_le_pairLog (r k : ℕ) (hr : 1 ≤ r) (hrk : r ≤ k) :
    Real.log (r : ℝ) ≤ cycleFactor k := by
  have hk : 1 ≤ k := hr.trans hrk
  have hlogk : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hk)
  have htwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
    norm_num at ht
    exact ht
  have hlog : Real.log (r : ℝ) ≤ Real.log (k : ℝ) :=
    Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)) (Nat.cast_le.mpr hrk)
  have hbase : Real.log (k : ℝ) ≤ Real.logb 2 (8 * (k : ℝ)) := by
    rw [Real.logb, log_eight_mul_nat k hk]
    apply (le_div_iff₀ log_two_pos).mpr
    nlinarith [mul_le_mul_of_nonneg_left htwo hlogk, log_two_pos]
  have hceil := Nat.le_ceil (Real.logb 2 (8 * (k : ℝ)))
  have htot := (hlog.trans hbase).trans hceil
  have hceil' : (⌈Real.logb 2 (8 * (k : ℝ))⌉₊ : ℝ) ≤ cycleFactor k := by
    simp only [cycleFactor, Nat.cast_add, Nat.cast_one]
    linarith
  exact htot.trans hceil'

end OnlineSteinerForest.UpperBound
