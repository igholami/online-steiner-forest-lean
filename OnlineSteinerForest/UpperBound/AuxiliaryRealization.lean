import OnlineSteinerForest.Graph.Comparison
import OnlineSteinerForest.Graph.ResidualBounds

/-! Realizing paths are actual simple input-graph paths, chosen inside a finite lifetime forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def realizingEdges (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (s t : V)
    (hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t) : Finset (Sym2 V) :=
  Classical.choose (exists_pathEdges_subset hF hr)

theorem realizingEdges_spec (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (s t : V)
    (hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t) :
    IsPathEdges G s t (realizingEdges G F hF s t hr) ∧ realizingEdges G F hF s t hr ⊆ F :=
  Classical.choose_spec (exists_pathEdges_subset hF hr)

theorem realizingEdges_cost_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (s t : V)
    (hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t) :
    edgeCost c (realizingEdges G F hF s t hr) ≤ edgeCost c F :=
  Finset.sum_le_sum_of_subset_of_nonneg (realizingEdges_spec G F hF s t hr).2
    (fun e he _ => hc e (hF e he))

end OnlineSteinerForest.UpperBound
