import OnlineSteinerForest.Graph.ResidualMetric
import Mathlib.Basic.ENNReal.Real

/-! Extend actual residual distances by infinity between disconnected components.
This gives a globally defined distance for charging-graph projections. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def residualEDistance (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (u v : V) : ENNReal := by
  classical
  exact if h : G.Reachable u v then ENNReal.ofReal (residualDistance G c B u v h) else ⊤

theorem residualEDistance_of_reachable (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (u v : V) (h : G.Reachable u v) :
    residualEDistance G c B u v = ENNReal.ofReal (residualDistance G c B u v h) := by
  simp [residualEDistance, h]

theorem residualEDistance_of_not_reachable (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (u v : V) (h : ¬ G.Reachable u v) :
    residualEDistance G c B u v = ⊤ := by simp [residualEDistance, h]

theorem residualEDistance_refl (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V)) (u : V) :
    residualEDistance G c B u u = 0 := by
  have hr : G.Reachable u u := ⟨.nil⟩
  rw [residualEDistance_of_reachable G c B u u hr]
  have hnil : IsPathEdges G u u ∅ := ⟨.nil, SimpleGraph.Walk.IsPath.nil, by simp⟩
  have hmin := (shortestPathEdges_spec G c B u u hr).2 ∅ hnil
  have hle : residualDistance G c B u u hr ≤ 0 := by
    simpa [residualDistance, residualCost] using hmin
  have heq := le_antisymm hle (residualDistance_nonneg G c hc B u u hr)
  simp [heq]

theorem residualEDistance_symm (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (u v : V) :
    residualEDistance G c B u v = residualEDistance G c B v u := by
  classical
  by_cases h : G.Reachable u v
  · rw [residualEDistance_of_reachable G c B u v h,
      residualEDistance_of_reachable G c B v u h.symm, residualDistance_symm G c B u v h]
  · have hv : ¬ G.Reachable v u := fun hv => h hv.symm
    rw [residualEDistance_of_not_reachable G c B u v h,
      residualEDistance_of_not_reachable G c B v u hv]

theorem residualEDistance_triangle (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V)) (u v w : V) :
    residualEDistance G c B u w ≤ residualEDistance G c B u v + residualEDistance G c B v w := by
  classical
  by_cases huv : G.Reachable u v
  · by_cases hvw : G.Reachable v w
    · rw [residualEDistance_of_reachable G c B u w (huv.trans hvw),
        residualEDistance_of_reachable G c B u v huv,
        residualEDistance_of_reachable G c B v w hvw]
      have hh := ENNReal.ofReal_le_ofReal (residualDistance_triangle G c hc B u v w huv hvw)
      rw [ENNReal.ofReal_add (residualDistance_nonneg G c hc B u v huv)
        (residualDistance_nonneg G c hc B v w hvw)] at hh
      exact hh
    · rw [residualEDistance_of_not_reachable G c B v w hvw, add_top]
      exact le_top
  · rw [residualEDistance_of_not_reachable G c B u v huv, top_add]
    exact le_top

end OnlineSteinerForest.UpperBound
