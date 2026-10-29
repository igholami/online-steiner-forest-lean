import OnlineSteinerForest.UpperBound.FinalParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The explicit walk length in the weighted cycle-rank estimate. -/
namespace OnlineSteinerForest.UpperBound.Girth

theorem eight_mul_le_pow_log_ceil (r : ℕ) (hr : 1 ≤ r) :
    (8 * r : ℝ) ≤ (2 : ℝ) ^ ⌈Real.logb 2 (8 * r : ℝ)⌉₊ := by
  have hx : (0 : ℝ) < 8 * r := by positivity
  have hh := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp
    (Nat.le_ceil (Real.logb 2 (8 * r : ℝ)))
  simpa only [Real.rpow_natCast] using hh

theorem rank_length_dominates_vertices (r vertices : ℕ) (hr : 1 ≤ r) (hv : vertices ≤ 2 * r) :
    2 * (vertices : ℝ) < (2 : ℝ) ^ ⌈Real.logb 2 (8 * r : ℝ)⌉₊ := by
  have hh := eight_mul_le_pow_log_ceil r hr
  have hv' : (vertices : ℝ) ≤ 2 * r := by exact_mod_cast hv
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

end OnlineSteinerForest.UpperBound.Girth
