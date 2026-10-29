import OnlineSteinerForest.LowerBound.BadPrice
import OnlineSteinerForest.LowerBound.Probability.BadRank
import Mathlib.Tactic.Ring

/-! Linearity of the actual uniform-permutation mean discarded price. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

open Probability
open scoped Classical

noncomputable def meanBadPrice (h : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (2 * matchingSize h)), badPrice h σ) /
    Fintype.card (Equiv.Perm (Fin (2 * matchingSize h)))

theorem badPrice_eq_sum_indicator (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    badPrice h σ = ∑ i ∈ positiveRanks h, rankPrice h i *
      indicator (fun σ => ¬ GoodRank h σ i) σ := by
  unfold badPrice badRanks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hg : GoodRank h σ i <;> simp [indicator, hg]

theorem meanBadPrice_eq_sum (h : ℕ) :
    meanBadPrice h = ∑ i ∈ positiveRanks h, rankPrice h i * badRankProbability h i := by
  unfold meanBadPrice
  simp_rw [badPrice_eq_sum_indicator]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  unfold badRankProbability
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

end OnlineSteinerForest.LowerBound
