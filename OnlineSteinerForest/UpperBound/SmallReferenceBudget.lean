import OnlineSteinerForest.UpperBound.SmallComponentBudget

/-! Sum the disjoint small reference-tree budgets without duplicating original costs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem small_reference_budget_of_threshold (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (hk : 1 ≤ requests.length)
    (F : Finset (Sym2 V)) (hinput : ∀ e ∈ F, e ∈ G.edgeSet)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (hscale : 0 < scale)
    (hband : ∀ i ∈ batch, payment G c requests feasible i ≤ 2 * scale)
    (hthreshold : ∀ C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent,
      ((componentPairs F requests (smallReferencePairs c requests F batch scale) C).card : ℝ) * scale ≤
        4 * cycleFactor (componentPairs F requests (smallReferencePairs c requests F batch scale) C).card *
          edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C)) :
    (∑ i ∈ smallReferencePairs c requests F batch scale, payment G c requests feasible i) ≤
      288 * cycleFactor (cycleFactor requests.length) * edgeCost c F := by
  rw [← sum_componentPairs F requests (smallReferencePairs c requests F batch scale)
    (payment G c requests feasible)]
  calc
    _ ≤ ∑ C ∈ referenceComponents (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))),
        288 * cycleFactor (cycleFactor requests.length) *
          edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C) := by
      apply Finset.sum_le_sum
      intro C _
      exact small_component_budget_of_threshold G c hc requests feasible hk F hinput batch
        scale hscale hband C (hthreshold C)
    _ = 288 * cycleFactor (cycleFactor requests.length) *
        (∑ C ∈ referenceComponents (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))),
          edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C)) :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by rw [sum_reference_component_costs F hinput c]

end OnlineSteinerForest.UpperBound
