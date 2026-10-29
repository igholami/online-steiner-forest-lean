import OnlineSteinerForest.UpperBound.ReferenceClassRun

/-! Every future pair remains connected in the computed class reference forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem classReference_connects_future (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) (i : Fin requests.length)
    (hi : i ∈ futurePairs G c requests feasible r b) :
    (SimpleGraph.fromEdgeSet (((classReference G c hc requests feasible r b).val :
      Finset (Sym2 V)) : Set (Sym2 V))).Reachable requests[i.val].1 requests[i.val].2 := by
  obtain ⟨hu, hv⟩ := future_pair_endpoints_marked G c requests feasible r b i hi
  apply referenceRun_preserves_future G c hc (initialReference G c hc requests feasible)
    (initialReference_spec G c hc requests feasible).1.1 (futureMarks G c requests feasible r)
    (futureMarks_antitone G c requests feasible r) b hu hv
  exact (initialReference_spec G c hc requests feasible).1.2 requests[i.val] (List.getElem_mem i.isLt)

end OnlineSteinerForest.UpperBound
