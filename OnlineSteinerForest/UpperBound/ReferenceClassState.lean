import OnlineSteinerForest.UpperBound.ReferenceClassRun

/-! The reference states are actual forests and their successor is the implemented update. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem classReference_isAcyclic (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    (SimpleGraph.fromEdgeSet (((classReference G c hc requests feasible r b).val :
      Finset (Sym2 V)) : Set (Sym2 V))).IsAcyclic := by
  cases b with
  | zero => exact (initialReference_spec G c hc requests feasible).2.1
  | succ b =>
    exact (referenceUpdate_spec G c hc
      (classReference G c hc requests feasible r b).val
      (classReference G c hc requests feasible r b).property
      (futureMarks G c requests feasible r b)).2.1

theorem classReference_succ (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    (classReference G c hc requests feasible r (b + 1)).val =
      referenceUpdate G c hc (classReference G c hc requests feasible r b).val
        (classReference G c hc requests feasible r b).property (futureMarks G c requests feasible r b) :=
  rfl

end OnlineSteinerForest.UpperBound
