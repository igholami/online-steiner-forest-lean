import OnlineSteinerForest.UpperBound.SmallReferenceBudget
import OnlineSteinerForest.UpperBound.ThresholdMain

/-! The actual small-tree payment bound with every threshold hypothesis discharged. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem small_reference_payment_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (hk : 1 ≤ requests.length)
    (F : Finset (Sym2 V)) (hinput : ∀ e ∈ F, e ∈ G.edgeSet)
    (batch : Finset (Fin requests.length)) (scale : ℝ) (hscale : 0 < scale)
    (hconnect : ∀ i ∈ batch, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable
      requests[i.val].1 requests[i.val].2)
    (hband : ∀ i ∈ batch, scale ≤ payment G c requests feasible i ∧
      payment G c requests feasible i ≤ 2 * scale) :
    (∑ i ∈ smallReferencePairs c requests F batch scale, payment G c requests feasible i) ≤
      288 * cycleFactor (cycleFactor requests.length) * edgeCost c F := by
  apply small_reference_budget_of_threshold G c hc requests feasible hk F hinput batch scale
    hscale (fun i hi => (hband i hi).2)
  intro C
  apply request_count_mul_separation_le G c hc requests feasible
    (componentPairs F requests (smallReferencePairs c requests F batch scale) C)
    (componentEdges (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))) C)
    (fun e he => hinput e (reference_componentEdges_subset F C he))
    (componentPairs_connected F requests _ (fun i hi => hconnect i (Finset.mem_filter.mp hi).1) C)
    scale hscale
  intro i hi
  exact (hband i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1).1

end OnlineSteinerForest.UpperBound
