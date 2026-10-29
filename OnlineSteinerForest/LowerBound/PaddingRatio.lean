import OnlineSteinerForest.LowerBound.PaddingLevel
import OnlineSteinerForest.LowerBound.CompetitiveRatio

/-! The same instance supports the logarithmic ratio at every length before the next scale. -/
namespace OnlineSteinerForest.LowerBound
variable [OnlineSteinerForest.PathSelection.{0}]


theorem instance_padding_ratio (k h : ℕ) (hh : 32 ≤ h) (hk : vertexCount 32 ≤ k)
    (hupper : k < vertexCount (h + 1))
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    (lowerConstant / 4) *
      optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) * Real.log k * Real.log (Real.log k) ≤
      greedyCost (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) := by
  obtain ⟨hlog0, hlog, hll⟩ := padding_log_bounds k h hh hk hupper
  have hprod : Real.log k * Real.log (Real.log k) ≤
      (2 * (logSize h : ℝ) * Real.log 2) * (2 * (h : ℝ) * Real.log 2) :=
    (mul_le_mul_of_nonneg_left hll hlog0).trans
      (mul_le_mul_of_nonneg_right hlog (by positivity))
  have hO := optimalEdges_feasible (instanceGraph h σ) (constructionCost (rankPrice h))
    (instanceRequests h σ) (instance_feasible h σ)
  have hOpt : 0 ≤ optimum (instanceGraph h σ) (constructionCost (rankPrice h))
      (instanceRequests h σ) (instance_feasible h σ) :=
    Finset.sum_nonneg (fun e he => (instance_positive h σ e (hO.1 e he)).le)
  calc
    _ = ((lowerConstant / 4) * optimum (instanceGraph h σ)
        (constructionCost (rankPrice h)) (instanceRequests h σ) (instance_feasible h σ)) *
        (Real.log k * Real.log (Real.log k)) := by ring
    _ ≤ ((lowerConstant / 4) * optimum (instanceGraph h σ)
        (constructionCost (rankPrice h)) (instanceRequests h σ) (instance_feasible h σ)) *
        ((2 * (logSize h : ℝ) * Real.log 2) * (2 * (h : ℝ) * Real.log 2)) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (div_nonneg lowerConstant_pos.{0}.le (by norm_num)) hOpt)
    _ = optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) * ((logSize h : ℝ) * h * Real.log 2 / 8192) := by
      unfold lowerConstant
      field_simp [(Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'] <;> ring
    _ ≤ _ := instance_scale_lower_bound h hh σ hσ

end OnlineSteinerForest.LowerBound
