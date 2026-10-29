import OnlineSteinerForest.UpperBound.ZonesInterstarForest

/-! Original component connections route through the chosen actual interstar links. -/
namespace OnlineSteinerForest.UpperBound.InterstarForest

open scoped Classical

variable {V X : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {centers : Finset V} {stars : StarContraction G centers}

/-- Realizing the selected interstar edges connects the assigned centers of
all originally connected core zones. -/
theorem route_core_connections (f : InterstarForest stars) (R : SimpleGraph X)
    (centerAnchor : ↥centers → X)
    (hlinks : ∀ e : ↥f.graph.edgeFinset,
      R.Reachable (centerAnchor (stars.assign (f.left e)))
        (centerAnchor (stars.assign (f.right e))))
    {u v : V} (huv : G.Reachable u v) :
    R.Reachable (centerAnchor (stars.assign u)) (centerAnchor (stars.assign v)) := by
  have ht : f.graph.Reachable (stars.assign u) (stars.assign v) := by
    rw [f.reachable]
    exact stars.quotient_reachable_iff u v |>.mpr huv
  apply reachable_from_edge_routes f.graph R centerAnchor ?_ ht
  intro a b hab
  let e : ↥f.graph.edgeFinset := ⟨s(a, b), SimpleGraph.mem_edgeFinset.mpr hab⟩
  have hp : s(stars.assign (f.left e), stars.assign (f.right e)) = s(a, b) := f.projects e
  rcases Sym2.eq_iff.mp hp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simpa only [ha, hb] using hlinks e
  · have hrev : R.Reachable (centerAnchor b) (centerAnchor a) := by
      simpa only [ha, hb] using hlinks e
    exact hrev.symm

end OnlineSteinerForest.UpperBound.InterstarForest
