import OnlineSteinerForest.UpperBound.ReferenceInitial
import OnlineSteinerForest.UpperBound.ReferenceInvariant
import OnlineSteinerForest.UpperBound.ReferenceFutureSets

/-! Each residue class has its own actual evolving original-edge reference forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def classReference (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    {F : Finset (Sym2 V) // ∀ e ∈ F, e ∈ G.edgeSet} :=
  referenceRun G c hc (initialReference G c hc requests feasible)
    (initialReference_spec G c hc requests feasible).1.1 (futureMarks G c requests feasible r) b

theorem classReference_cost_le_optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    edgeCost c (classReference G c hc requests feasible r b).val ≤ optimum G c requests feasible := by
  apply (referenceRun_cost_le_initial G c hc (initialReference G c hc requests feasible)
    (initialReference_spec G c hc requests feasible).1.1
    (futureMarks G c requests feasible r) b).trans
  exact (initialReference_spec G c hc requests feasible).2.2.le

theorem classReference_connects_batch (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r) (i : Fin requests.length)
    (hi : i ∈ costBatch G c requests feasible b) :
    (SimpleGraph.fromEdgeSet (((classReference G c hc requests feasible r b.val).val :
      Finset (Sym2 V)) : Set (Sym2 V))).Reachable requests[i.val].1 requests[i.val].2 := by
  have hfut (j : ℕ) (hj : j < b.val) : i ∈ futurePairs G c requests feasible r j :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, b, hb, hj, hi⟩
  apply referenceRun_preserves_each G c hc (initialReference G c hc requests feasible)
    (initialReference_spec G c hc requests feasible).1.1
    (futureMarks G c requests feasible r) b.val
    (fun j hj => (future_pair_endpoints_marked G c requests feasible r j i (hfut j hj)).1)
    (fun j hj => (future_pair_endpoints_marked G c requests feasible r j i (hfut j hj)).2)
  exact (initialReference_spec G c hc requests feasible).1.2 requests[i.val]
    (List.getElem_mem i.isLt)

end OnlineSteinerForest.UpperBound
