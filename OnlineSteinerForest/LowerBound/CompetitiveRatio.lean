import OnlineSteinerForest.LowerBound.ScaleRatio
import OnlineSteinerForest.LowerBound.RequestLogs

/-! The logarithmic lower bound for every successful ordered matching. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

noncomputable def lowerConstant : ℝ := 1 / (8192 * Real.log 2)

theorem lowerConstant_pos : 0 < lowerConstant := by
  unfold lowerConstant
  exact div_pos (by norm_num) (mul_pos (by norm_num) (Real.log_pos (by norm_num)))

theorem instance_competitive_lower_bound (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    lowerConstant * optimum (instanceGraph h σ) (constructionCost (rankPrice h))
        (instanceRequests h σ) (instance_feasible h σ) * Real.log (instanceRequests h σ).length *
        Real.log (Real.log (instanceRequests h σ).length) ≤
      greedyCost (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) := by
  obtain ⟨hlog0, hlog, hloglog⟩ := instance_request_log_bounds h hh σ hσ
  have hprod : Real.log (instanceRequests h σ).length *
      Real.log (Real.log (instanceRequests h σ).length) ≤
      ((logSize h : ℝ) * Real.log 2) * ((h : ℝ) * Real.log 2) :=
    (mul_le_mul_of_nonneg_left hloglog hlog0).trans
      (mul_le_mul_of_nonneg_right hlog (by positivity))
  have hO := optimalEdges_feasible (instanceGraph h σ) (constructionCost (rankPrice h))
    (instanceRequests h σ) (instance_feasible h σ)
  have hOpt : 0 ≤ optimum (instanceGraph h σ) (constructionCost (rankPrice h))
      (instanceRequests h σ) (instance_feasible h σ) :=
    Finset.sum_nonneg (fun e he => (instance_positive h σ e (hO.1 e he)).le)
  calc
    _ = (lowerConstant * optimum (instanceGraph h σ) (constructionCost (rankPrice h))
        (instanceRequests h σ) (instance_feasible h σ)) *
        (Real.log (instanceRequests h σ).length * Real.log (Real.log (instanceRequests h σ).length)) := by ring
    _ ≤ (lowerConstant * optimum (instanceGraph h σ) (constructionCost (rankPrice h))
        (instanceRequests h σ) (instance_feasible h σ)) *
        (((logSize h : ℝ) * Real.log 2) * ((h : ℝ) * Real.log 2)) :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg lowerConstant_pos.le hOpt)
    _ = optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) * ((logSize h : ℝ) * h * Real.log 2 / 8192) := by
      unfold lowerConstant
      field_simp [(Real.log_pos (show (1 : ℝ) < 2 by norm_num)).ne'] <;> ring
    _ ≤ _ := instance_scale_lower_bound h hh σ hσ

end OnlineSteinerForest.LowerBound
