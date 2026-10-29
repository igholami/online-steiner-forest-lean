import OnlineSteinerForest.LowerBound.GreedyCost
import OnlineSteinerForest.LowerBound.OfflineBound
import OnlineSteinerForest.LowerBound.PriceLowerBound

/-! Competitive ratio in the natural size parameters of the lower construction. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem instance_scale_lower_bound (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
      (instance_feasible h σ) * ((logSize h : ℝ) * h * Real.log 2 / 8192) ≤
      greedyCost (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) := by
  have hs : 0 ≤ (logSize h : ℝ) * h * Real.log 2 / 8192 := by positivity
  calc
    _ ≤ ((vertexCount h : ℝ) - 1) * ((logSize h : ℝ) * h * Real.log 2 / 8192) :=
      mul_le_mul_of_nonneg_right (instance_optimum_le_path h σ) hs
    _ ≤ (vertexCount h : ℝ) * ((logSize h : ℝ) * h * Real.log 2 / 8192) :=
      mul_le_mul_of_nonneg_right (by linarith) hs
    _ = (vertexCount h : ℝ) * logSize h * h * Real.log 2 / 8192 := by ring
    _ ≤ totalPrice h / 2 := by
      have ht := totalPrice_lower h hh
      norm_num at ht ⊢
      linarith
    _ ≤ _ := instance_greedy_cost_ge_half h σ hσ

end OnlineSteinerForest.LowerBound
