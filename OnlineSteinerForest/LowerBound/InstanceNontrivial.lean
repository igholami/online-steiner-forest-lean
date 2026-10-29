import OnlineSteinerForest.LowerBound.RequestGrowth
import OnlineSteinerForest.Graph.Positive

/-! Successful lower-bound instances have a genuinely positive offline optimum. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem instance_optimum_pos (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    0 < optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
      (instance_feasible h σ) := by
  have hg := instance_request_count_ge_level h hh σ hσ
  have hcard : 0 < (retainedRanks h σ).card := by
    simp only [instanceRequests, requestedPairs_length] at hg
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcard
  have hqin : (Sum.inl (leftEndpoint σ i), Sum.inl (rightEndpoint σ i)) ∈ instanceRequests h σ := by
    apply List.mem_map.mpr
    exact ⟨i, (Finset.mem_sort (· ≤ ·)).mpr hi, rfl⟩
  exact optimum_pos _ _ (instance_positive h σ) _ (instance_feasible h σ) _ hqin
    (by simpa only [ne_eq, Sum.inl.injEq] using endpoints_ne σ i)

end OnlineSteinerForest.LowerBound
