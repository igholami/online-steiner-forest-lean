import OnlineSteinerForest.LowerBound.ExpectedBadPrice
import OnlineSteinerForest.LowerBound.ExpectedBudget
import OnlineSteinerForest.LowerBound.Probability.BadRankBound

/-! The manuscript's probabilistic existence argument produces an actual successful matching. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem exists_retaining_matching (h : ℕ) (hh : 32 ≤ h) :
    ∃ σ : Equiv.Perm (Fin (2 * matchingSize h)), RetainsHalf h σ := by
  have hmean := meanBadPrice_bound_of_rank_bounds h hh (Probability.badRankProbability_le h hh)
  have hlt : meanBadPrice h < totalPrice h / 2 := hmean.trans_lt (expected_budget_lt_half h hh)
  have hden : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin (2 * matchingSize h))) :=
    Nat.cast_pos.mpr Fintype.card_pos
  apply exists_retainsHalf_of_mean_bad h
  have hnorm : (∑ σ : Equiv.Perm (Fin (2 * matchingSize h)), badPrice h σ) /
      Fintype.card (Equiv.Perm (Fin (2 * matchingSize h))) ≤ totalPrice h / 2 := hlt.le
  simpa only [mul_comm] using (div_le_iff₀ hden).mp hnorm

end OnlineSteinerForest.LowerBound
