import OnlineSteinerForest.UpperBound.SmallComponentCosts
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceSplit

/-! Identify the computed reference-tree price with its original ambient edge cost. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem componentEdges_cost (G : SimpleGraph V) (C : G.ConnectedComponent) (c : Sym2 V → ℝ) :
    edgeCost c (componentEdges G C) =
      graphCost C.toSimpleGraph (fun e => c (Sym2.map Subtype.val e)) := by
  rw [graphCost_eq_edgeFinset]
  simp only [componentEdges, edgeCost, Finset.sum_map]
  rfl

theorem referenceTreeCost_eq_component_cost (F : Finset (Sym2 V)) (c : Sym2 V → ℝ) (r : V) :
    referenceTreeCost F c r = edgeCost c (componentEdges
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 V)))
      ((SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).connectedComponentMk r)) :=
  (componentEdges_cost _ _ c).symm

theorem edgeFinset_of_input {G : SimpleGraph V} (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).edgeFinset = F := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.edgeFinset, Set.mem_toFinset]
    change (s(u, v) ∈ F ∧ u ≠ v) ↔ s(u, v) ∈ F
    exact ⟨And.left, fun h => ⟨h, (hF _ h).ne⟩⟩

theorem sum_reference_component_costs {G : SimpleGraph V} (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (c : Sym2 V → ℝ) :
    (∑ C ∈ referenceComponents (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))),
      edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C)) = edgeCost c F := by
  apply (sum_component_costs (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) c).trans
  congr 1
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [SimpleGraph.edgeFinset, Set.mem_toFinset]
    change (s(u, v) ∈ F ∧ u ≠ v) ↔ s(u, v) ∈ F
    exact ⟨And.left, fun h => ⟨h, (hF _ h).ne⟩⟩

end OnlineSteinerForest.UpperBound
