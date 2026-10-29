import OnlineSteinerForest.LowerBound.Tests
import OnlineSteinerForest.LowerBound.PriceSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exponential prefactor in the weighted alternate-path count. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem half_lt_log_two : (1 / 2 : ℝ) < Real.log 2 := by
  have hh := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
  rw [Real.log_inv] at hh
  norm_num at hh
  linarith

theorem exp_logSize_le (h : ℕ) :
    Real.exp ((logSize h : ℝ) / 64) ≤ (vertexCount h : ℝ) ^ (1 / 32 : ℝ) := by
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (vertexCount_pos h))]
  apply Real.exp_le_exp.mpr
  simp only [vertexCount, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  nlinarith [mul_le_mul_of_nonneg_left (le_of_lt half_lt_log_two)
    (show (0 : ℝ) ≤ logSize h from Nat.cast_nonneg _)]

theorem tilt_mul_rankPrice (h : ℕ) (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
    16 * ((i.val + 1 : ℕ) : ℝ) / matchingSize h * rankPrice h i = (logSize h : ℝ) / 64 := by
  unfold rankPrice
  rw [cast_price_of_ge h _ hi]
  have hm : (matchingSize h : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hi' : (((i.val + 1 : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

theorem exp_tilt_price_le (h : ℕ) (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
    Real.exp (16 * ((i.val + 1 : ℕ) : ℝ) / matchingSize h * rankPrice h i) ≤
      (vertexCount h : ℝ) ^ (1 / 32 : ℝ) := by
  rw [tilt_mul_rankPrice h i hi]
  exact exp_logSize_le h

end OnlineSteinerForest.LowerBound
