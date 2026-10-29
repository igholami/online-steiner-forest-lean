import OnlineSteinerForest.LowerBound.ComparisonPath
import OnlineSteinerForest.LowerBound.Instance
import OnlineSteinerForest.LowerBound.Size

/-! Offline optimum of the actual lower-bound instance is at most the unit path cost. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem instance_optimum_le_path (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
      (instance_feasible h σ) ≤ (vertexCount h : ℝ) - 1 := by
  calc
    _ ≤ edgeCost (constructionCost (rankPrice h)) (comparisonEdges (matchingSize h)) :=
      optimum_le _ _ _ _ _ (comparisonEdges_feasible σ (retainedRanks h σ))
    _ = ((2 * matchingSize h - 1 : ℕ) : ℝ) := comparisonEdges_cost _
    _ = _ := by
      rw [twice_matchingSize, Nat.cast_sub (vertexCount_pos h), Nat.cast_one]

end OnlineSteinerForest.LowerBound
