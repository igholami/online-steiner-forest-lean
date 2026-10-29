import OnlineSteinerForest.UpperBound.SmallPairSums
import OnlineSteinerForest.UpperBound.SmallTreeBudget
import OnlineSteinerForest.UpperBound.HistoryPayments

/-! Charge actual small requests in one reference component using the threshold estimate. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem small_component_budget_of_threshold (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (hk : 1 ≤ requests.length)
    (F : Finset (Sym2 V)) (hinput : ∀ e ∈ F, e ∈ G.edgeSet)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (hscale : 0 < scale)
    (hband : ∀ i ∈ batch, payment G c requests feasible i ≤ 2 * scale)
    (C : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).ConnectedComponent)
    (hthreshold : ((componentPairs F requests (smallReferencePairs c requests F batch scale) C).card : ℝ) * scale ≤
      4 * cycleFactor (componentPairs F requests (smallReferencePairs c requests F batch scale) C).card *
        edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C)) :
    (∑ i ∈ componentPairs F requests (smallReferencePairs c requests F batch scale) C,
      payment G c requests feasible i) ≤ 288 * cycleFactor (cycleFactor requests.length) *
        edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C) := by
  let selected := componentPairs F requests (smallReferencePairs c requests F batch scale) C
  have hcost : 0 ≤ edgeCost c (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C) := by
    apply Finset.sum_nonneg
    intro e he
    exact hc e (hinput e (reference_componentEdges_subset F C he))
  by_cases hne : selected.Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hiSmall := (Finset.mem_filter.mp hi).1
    have hsmall := (Finset.mem_filter.mp hiSmall).2
    rw [referenceTreeCost_eq_component_cost, (Finset.mem_filter.mp hi).2] at hsmall
    apply small_tree_payment_budget (cycleFactor requests.length) selected.card
      (four_le_cycleFactor requests.length hk) scale _ _ hscale hcost hsmall hthreshold
    calc
      _ ≤ ∑ _i ∈ selected, (2 * scale) := by
        apply Finset.sum_le_sum
        intro j hj
        exact hband j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      _ = 2 * selected.card * scale := by simp; ring
  · have hz : selected = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    change (∑ i ∈ selected, payment G c requests feasible i) ≤ _
    rw [hz, Finset.sum_empty]
    positivity

end OnlineSteinerForest.UpperBound
