import Mathlib.NumberTheory.Harmonic.Bounds

/-! Integral estimates for the harmonic tails used in the lower-bound prices. -/
namespace OnlineSteinerForest.LowerBound

theorem log_div_le_sum_inv (a b : ℕ) (ha : 0 < a) (hab : a ≤ b + 1) :
    Real.log (((b + 1 : ℕ) : ℝ) / a) ≤ ∑ i ∈ Finset.Icc a b, (i : ℝ)⁻¹ := by
  have ha' : (0 : ℝ) < a := Nat.cast_pos.mpr ha
  have hab' : (a : ℝ) ≤ (b + 1 : ℕ) := Nat.cast_le.mpr hab
  have hzero : (0 : ℝ) ∉ Set.uIcc (a : ℝ) ((b + 1 : ℕ) : ℝ) := by
    rw [Set.uIcc_of_le hab']
    intro hz
    exact (not_le_of_gt ha') hz.1
  calc
    _ = ∫ x in (a : ℝ)..((b + 1 : ℕ) : ℝ), x⁻¹ := (integral_inv hzero).symm
    _ ≤ _ := by
      simpa only [Finset.Ico_add_one_right_eq_Icc] using
        (inv_antitoneOn_Icc_right ha').integral_le_sum_Ico hab

end OnlineSteinerForest.LowerBound
