import OnlineSteinerForest.UpperBound.NearestNeighborComponent

/-! Component insertion bounds charged to the original finite forest-edge cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem graphCost_fromEdgeSet_le (B : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ B, 0 ≤ c e) :
    graphCost (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))) c ≤ edgeCost c B := by
  rw [graphCost_eq_edgeFinset]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    have heG := SimpleGraph.mem_edgeFinset.mp he
    have heG' : e ∈ (B : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa only [SimpleGraph.edgeSet_fromEdgeSet] using heG
    exact heG'.1
  · intro e he hnot
    exact hc e he

/-- The standard connected-component tree incurs no more cost than its ambient forest. -/
theorem component_graphCost_le (F : SimpleGraph V) (C : F.ConnectedComponent)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) :
    graphCost C.toSimpleGraph (fun e => c (Sym2.map Subtype.val e)) ≤ graphCost F c :=
  induced_cost_le F c hc C.supp

end OnlineSteinerForest.UpperBound
