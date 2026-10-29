import OnlineSteinerForest.LowerBound.Tests
import OnlineSteinerForest.LowerBound.Probability.WeightedUnion

/-! The uniform finite-permutation probability that a rank fails its distance test. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

noncomputable def badRankProbability (h : ℕ) (i : Fin (matchingSize h)) : ℝ :=
  (∑ σ : Equiv.Perm (Fin (2 * matchingSize h)),
    indicator (fun σ => ¬ GoodRank h σ i) σ) /
      Fintype.card (Equiv.Perm (Fin (2 * matchingSize h)))

theorem badRankProbability_nonneg (h : ℕ) (i : Fin (matchingSize h)) :
    0 ≤ badRankProbability h i := by
  unfold badRankProbability
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => indicator_nonneg _ _)) (Nat.cast_nonneg _)

end OnlineSteinerForest.LowerBound.Probability
