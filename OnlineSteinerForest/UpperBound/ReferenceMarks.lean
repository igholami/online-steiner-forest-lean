import OnlineSteinerForest.Graph.Feasibility
import Mathlib.Data.Finset.Prod

/-! The exact marked connections an evolving reference forest must preserve. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [DecidableEq V]

noncomputable def markedRequests (F : Finset (Sym2 V)) (marks : Finset V) : List (V × V) :=
  ((marks ×ˢ marks).filter fun q =>
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable q.1 q.2).toList

theorem mem_markedRequests (F : Finset (Sym2 V)) (marks : Finset V) (u v : V) :
    (u, v) ∈ markedRequests F marks ↔ u ∈ marks ∧ v ∈ marks ∧
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v := by
  simp only [markedRequests, Finset.mem_toList, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨hu, hv⟩, hr⟩
    exact ⟨hu, hv, hr⟩
  · rintro ⟨hu, hv, hr⟩
    exact ⟨⟨hu, hv⟩, hr⟩

theorem markedRequests_feasible_edges {G : SimpleGraph V} (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) :
    FeasibleEdges G (markedRequests F marks) F := by
  refine ⟨hF, ?_⟩
  intro q hq
  exact ((mem_markedRequests F marks q.1 q.2).mp hq).2.2

theorem markedRequests_feasible {G : SimpleGraph V} (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) :
    ∀ q ∈ markedRequests F marks, G.Reachable q.1 q.2 := by
  intro q hq
  apply (((markedRequests_feasible_edges F hF marks).2 q hq).mono)
  intro u v huv
  exact hF _ huv.1

end OnlineSteinerForest.UpperBound
