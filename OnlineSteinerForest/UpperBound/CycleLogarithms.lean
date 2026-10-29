import OnlineSteinerForest.UpperBound.FinalParameters

/-! Elementary base-two logarithm bounds used to unroll multiplicity inequalities. -/
namespace OnlineSteinerForest.UpperBound

theorem half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
  norm_num at h
  exact h

theorem logb_two_le_two_mul (x : ℝ) (hx : 0 < x) : Real.logb 2 x ≤ 2 * x := by
  have hl := Real.log_le_sub_one_of_pos hx
  rw [Real.logb]
  apply (div_le_iff₀ log_two_pos).mpr
  have hp := mul_le_mul_of_nonneg_left half_le_log_two hx.le
  nlinarith

theorem logb_two_mul (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    Real.logb 2 (x * y) = Real.logb 2 x + Real.logb 2 y := by
  simp only [Real.logb, Real.log_mul hx.ne' hy.ne']
  ring

theorem logb_two_pow (n : ℕ) : Real.logb 2 ((2 : ℝ) ^ n) = n := by
  rw [Real.logb, Real.log_pow]
  field_simp

theorem seventeen_le_zoneLog (M : ℝ) (hM : 256 ≤ M) : 17 ≤ Real.logb 2 (512 * M) := by
  have hp : (2 : ℝ) ^ 17 ≤ 512 * M := by norm_num; linarith
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 2 ^ 17) hp
  rw [Real.log_pow] at hl
  norm_num at hl
  rw [Real.logb]
  exact (le_div_iff₀ log_two_pos).mpr hl

end OnlineSteinerForest.UpperBound
