import OnlineSteinerForest.UpperBound.ReferenceMarks
import OnlineSteinerForest.Graph.ForestOptimum

/-! A concrete canonical reference update preserving the old marked connections. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Choose an actual minimum-cost forest preserving exactly the required old
marked connections. Any manuscript surgery candidate bounds its cost from above. -/
noncomputable def referenceUpdate (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) : Finset (Sym2 V) :=
  (exists_optimal_forest G c hc (markedRequests F marks)
    (markedRequests_feasible F hF marks)).choose

theorem referenceUpdate_spec (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) :
    FeasibleEdges G (markedRequests F marks) (referenceUpdate G c hc F hF marks) ∧
      (SimpleGraph.fromEdgeSet ((referenceUpdate G c hc F hF marks : Finset (Sym2 V)) :
        Set (Sym2 V))).IsAcyclic ∧
      edgeCost c (referenceUpdate G c hc F hF marks) =
        optimum G c (markedRequests F marks) (markedRequests_feasible F hF marks) :=
  (exists_optimal_forest G c hc (markedRequests F marks)
    (markedRequests_feasible F hF marks)).choose_spec

theorem referenceUpdate_preserves (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V)
    {u v : V} (hu : u ∈ marks) (hv : v ∈ marks)
    (hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v) :
    (SimpleGraph.fromEdgeSet ((referenceUpdate G c hc F hF marks : Finset (Sym2 V)) :
      Set (Sym2 V))).Reachable u v :=
  (referenceUpdate_spec G c hc F hF marks).1.2 (u, v)
    ((mem_markedRequests F marks u v).mpr ⟨hu, hv, hr⟩)

end OnlineSteinerForest.UpperBound
