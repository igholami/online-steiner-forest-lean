import OnlineSteinerForest.LowerBound.RootBound
import OnlineSteinerForest.LowerBound.PriceLowerBound

/-! The discarded-price expectation budget is strictly below half the total auxiliary price. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem expected_budget_lt_half (h : ℕ) (hh : 32 ≤ h) :
    (logSize h : ℝ) * (vertexCount h : ℝ) ^ (1 / 32 : ℝ) /
      (2048 * (prefixFraction h : ℝ)) < totalPrice h / 2 := by
  have hL : (0 : ℝ) < logSize h := Nat.cast_pos.mpr (logSize_pos h)
  have hN : (0 : ℝ) < vertexCount h := Nat.cast_pos.mpr (vertexCount_pos h)
  have hhpos : 0 < h := by omega
  have hhR : (32 : ℝ) ≤ h := Nat.cast_le.mpr hh
  have hε : (0 : ℝ) < (prefixFraction h : ℝ) := Rat.cast_pos.mpr (prefixFraction_pos h hhpos)
  have heps : (prefixFraction h : ℝ) * logSize h = 256 * h := by
    simp only [prefixFraction, Rat.cast_div, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat]
    norm_num only [show (2 : ℝ) ^ 8 = 256 by norm_num]
    exact div_mul_cancel₀ _ hL.ne'
  have hlarge : 4 < (prefixFraction h : ℝ) * logSize h * h * Real.log 2 := by
    rw [heps]
    have hsq : (1024 : ℝ) ≤ (h : ℝ) ^ 2 := by nlinarith
    have hmul := mul_lt_mul_of_pos_left half_lt_log_two
      (mul_pos (show (0 : ℝ) < 256 by norm_num) (sq_pos_of_pos (Nat.cast_pos.mpr hhpos)))
    nlinarith
  have hcoef : 1 / (2048 * (prefixFraction h : ℝ)) <
      (logSize h : ℝ) * h * Real.log 2 / 8192 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hε)).mpr
    nlinarith
  calc
    _ ≤ (vertexCount h : ℝ) / (2048 * (prefixFraction h : ℝ)) :=
      div_le_div_of_nonneg_right (logSize_mul_root_le_vertexCount h hh) (by positivity)
    _ = (vertexCount h : ℝ) * (1 / (2048 * (prefixFraction h : ℝ))) := by ring
    _ < (vertexCount h : ℝ) * ((logSize h : ℝ) * h * Real.log 2 / 8192) :=
      mul_lt_mul_of_pos_left hcoef hN
    _ = (vertexCount h : ℝ) * logSize h * h * Real.log 2 / 8192 := by ring
    _ ≤ _ := by have ht := totalPrice_lower h hh; norm_num at ht ⊢; linarith

end OnlineSteinerForest.LowerBound
