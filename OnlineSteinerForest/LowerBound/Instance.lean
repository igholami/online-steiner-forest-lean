import OnlineSteinerForest.LowerBound.Tests
import OnlineSteinerForest.Greedy.Algorithm

/-! The actual positive-cost instance defined by an arbitrary ordered matching.
MatchingExistence.lean proves that some matching retains half the auxiliary price. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

noncomputable def instanceGraph (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :=
  constructionGraph σ (retainedRanks h σ)

noncomputable def instanceRequests (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :=
  requestedPairs σ (retainedRanks h σ)

theorem instance_feasible (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    ∀ q ∈ instanceRequests h σ, (instanceGraph h σ).Reachable q.1 q.2 :=
  requestedPairs_feasible σ (retainedRanks h σ)

theorem retained_price_pos (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (i : Fin (matchingSize h)) (hi : i ∈ retainedRanks h σ) : 0 < rankPrice h i := by
  classical
  have hfirst : firstRank h ≤ i.val + 1 := (Finset.mem_filter.mp hi).2.1
  have hm : 0 < matchingSize h := Nat.zero_lt_of_lt i.isLt
  have hp : (0 : ℚ) < price h (i.val + 1) := by
    rw [price_of_ge h _ hfirst]
    exact div_pos (mul_pos (Nat.cast_pos.mpr (logSize_pos h)) (Nat.cast_pos.mpr hm))
      (by positivity)
  unfold rankPrice
  exact_mod_cast hp

theorem instance_positive (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    ∀ e ∈ (instanceGraph h σ).edgeSet, 0 < constructionCost (rankPrice h) e :=
  constructionCost_pos σ _ _ (retained_price_pos h σ)

end OnlineSteinerForest.LowerBound
