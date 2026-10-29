import OnlineSteinerForest.LowerBound.Harmonic
import OnlineSteinerForest.UpperBound.Accounting
import Mathlib.Tactic.FieldSimp

/-! The inverse-square tail estimate used for the expected discarded price. -/
namespace OnlineSteinerForest.LowerBound

theorem inv_sq_le_inv_sub_inv (x : ℝ) (hx : 1 < x) :
    x⁻¹ ^ 2 ≤ (x - 1)⁻¹ - x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hm : 0 < x - 1 := sub_pos.mpr hx
  calc
    _ = 1 / x ^ 2 := by simp [one_div, inv_pow]
    _ ≤ 1 / (x * (x - 1)) := one_div_le_one_div_of_le (mul_pos hx0 hm) (by nlinarith)
    _ = _ := by field_simp [hx0.ne', hm.ne']; ring

theorem sum_inverse_square_range_le (a n : ℕ) (ha : 2 ≤ a) :
    (∑ j ∈ Finset.range n, (((a + j : ℕ) : ℝ)⁻¹) ^ 2) ≤ (((a - 1 : ℕ) : ℝ)⁻¹) := by
  have ht := UpperBound.total_savings_le_initial
    (fun j => (((a + j - 1 : ℕ) : ℝ)⁻¹)) n (by positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range n,
        ((((a + j - 1 : ℕ) : ℝ)⁻¹) - (((a + (j + 1) - 1 : ℕ) : ℝ)⁻¹)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [show a + (j + 1) - 1 = a + j by omega,
        Nat.cast_sub (show 1 ≤ a + j by omega), Nat.cast_one]
      exact inv_sq_le_inv_sub_inv _ (Nat.one_lt_cast.mpr (by omega))
    _ ≤ _ := by simpa only [Nat.add_zero] using ht

end OnlineSteinerForest.LowerBound
