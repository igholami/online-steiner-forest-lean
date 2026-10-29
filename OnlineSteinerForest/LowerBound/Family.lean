import OnlineSteinerForest.LowerBound.MatchingExistence
import OnlineSteinerForest.LowerBound.CompetitiveRatio
import OnlineSteinerForest.LowerBound.InstanceNontrivial

/-! The complete lower-bound family before reindexing vertices by `Fin n`. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem exists_large_lower_instance (K : ℕ) :
    ∃ h : ℕ, 32 ≤ h ∧ ∃ σ : Equiv.Perm (Fin (2 * matchingSize h)),
      RetainsHalf h σ ∧ max K 3 ≤ (instanceRequests h σ).length ∧
      0 < optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) ∧
      lowerConstant * optimum (instanceGraph h σ) (constructionCost (rankPrice h))
          (instanceRequests h σ) (instance_feasible h σ) * Real.log (instanceRequests h σ).length *
          Real.log (Real.log (instanceRequests h σ).length) ≤
        greedyCost (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
          (instance_feasible h σ) := by
  let h := max K 32
  have hh : 32 ≤ h := Nat.le_max_right _ _
  obtain ⟨σ, hσ⟩ := exists_retaining_matching h hh
  have hg := instance_request_count_ge_level h hh σ hσ
  refine ⟨h, hh, σ, hσ, ?_, instance_optimum_pos h hh σ hσ,
    instance_competitive_lower_bound h hh σ hσ⟩
  apply max_le
  · exact (Nat.le_max_left K 32).trans hg
  · exact (show 3 ≤ h by omega).trans hg

end OnlineSteinerForest.LowerBound
