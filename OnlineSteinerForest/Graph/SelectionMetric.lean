import OnlineSteinerForest.Graph.Residual

/-! Minimum residual distance does not depend on how minimizing paths are selected. -/
namespace OnlineSteinerForest

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

theorem residualDistance_selection_eq (p q : PathSelection.{u})
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s t : V) (h : G.Reachable s t) :
    (letI : PathSelection := p; residualDistance G c B s t h) =
    (letI : PathSelection := q; residualDistance G c B s t h) := by
  have hp := @PathSelection.spec p V _ _ G c B s t h
  have hq := @PathSelection.spec q V _ _ G c B s t h
  apply le_antisymm
  · exact hp.2 _ hq.1
  · exact hq.2 _ hp.1

end OnlineSteinerForest
