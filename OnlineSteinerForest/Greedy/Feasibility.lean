import OnlineSteinerForest.Greedy.Algorithm
import OnlineSteinerForest.Graph.Feasibility

/-! The implemented algorithm buys only input edges and fulfills every request. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem reachable_mono_edges {B F : Finset (Sym2 V)} (h : B ⊆ F) {s t : V}
    (hst : (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable s t) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t :=
  hst.mono (SimpleGraph.fromEdgeSet_mono (by exact h))

/-- Previously purchased edges are never removed. -/
theorem greedy_extends (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (B : Finset (Sym2 V)) :
    B ⊆ greedy G c requests feasible B := by
  induction requests generalizing B with
  | nil => exact Finset.Subset.refl _
  | cons q qs ih =>
    exact (greedyStep_mono G c B q.1 q.2 _).trans (ih _ _)

/-- Inductive feasibility, allowing an arbitrary already purchased input edge set. -/
theorem greedy_feasible_from (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) :
    FeasibleEdges G requests (greedy G c requests feasible B) := by
  induction requests generalizing B with
  | nil => exact ⟨hB, by simp⟩
  | cons q qs ih =>
    let next := greedyStep G c B q.1 q.2 (feasible q (by simp))
    have hpath := (shortestPathEdges_spec G c B q.1 q.2 (feasible q (by simp))).1
    have hnext : ∀ e ∈ next, e ∈ G.edgeSet := by
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hB e he
      · exact hpath.subset_edgeSet e he
    have hrest := ih (fun r hr => feasible r (by simp [hr])) next hnext
    refine ⟨hrest.1, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact reachable_mono_edges
        (Finset.subset_union_right.trans (greedy_extends G c qs _ next)) hpath.reachable
    · exact hrest.2 r hr

/-- Greedy returns a feasible offline solution for the requests it has seen. -/
theorem greedy_feasible (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    FeasibleEdges G requests (greedy G c requests feasible) :=
  greedy_feasible_from G c requests feasible ∅ (by simp)

end OnlineSteinerForest
