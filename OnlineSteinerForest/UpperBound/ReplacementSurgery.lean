import OnlineSteinerForest.Graph.Feasibility
import Mathlib.Tactic.Linarith

/-! Connectivity and original-cost accounting for an explicit edge replacement. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [DecidableEq V]

/-- Replacing every removed edge by a connecting walk preserves all old connections. -/
theorem replacement_preserves_reachable (F R A : Finset (Sym2 V))
    (hlocal : ∀ u v, s(u, v) ∈ R →
      (SimpleGraph.fromEdgeSet ((F \ R ∪ A : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v)
    {u v : V} (h : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v) :
    (SimpleGraph.fromEdgeSet ((F \ R ∪ A : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons u v z huv p ih =>
    apply SimpleGraph.Reachable.trans _ ih
    by_cases hr : s(u, v) ∈ R
    · exact hlocal u v hr
    · exact SimpleGraph.Adj.reachable ⟨Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨huv.1, hr⟩), huv.2⟩

theorem replacement_feasible {G : SimpleGraph V} {requests : List (V × V)}
    (F R A : Finset (Sym2 V)) (hF : FeasibleEdges G requests F)
    (hA : ∀ e ∈ A, e ∈ G.edgeSet)
    (hlocal : ∀ u v, s(u, v) ∈ R →
      (SimpleGraph.fromEdgeSet ((F \ R ∪ A : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v) :
    FeasibleEdges G requests (F \ R ∪ A) := by
  constructor
  · intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hF.1 e (Finset.mem_sdiff.mp he).1
    · exact hA e he
  · intro q hq
    exact replacement_preserves_reachable F R A hlocal (hF.2 q hq)

/-- The cost of all removed edges is a saving, up to the cost of the inserted edges. -/
theorem replacement_cost (c : Sym2 V → ℝ) (F R A : Finset (Sym2 V))
    (hRF : R ⊆ F) (hc : ∀ e, 0 ≤ c e) :
    edgeCost c (F \ R ∪ A) ≤ edgeCost c F - edgeCost c R + edgeCost c A := by
  have hpart : edgeCost c (F \ R) + edgeCost c R = edgeCost c F := by
    exact Finset.sum_sdiff hRF
  have hunion : edgeCost c (F \ R ∪ A) ≤ edgeCost c (F \ R) + edgeCost c A := by
    rw [edgeCost_union]
    apply add_le_add le_rfl
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (by intro e _ _; exact hc e)
  linarith

end OnlineSteinerForest.UpperBound
