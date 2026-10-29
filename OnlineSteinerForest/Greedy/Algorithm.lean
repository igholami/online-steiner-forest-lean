import OnlineSteinerForest.Graph.Paths

/-! Greedy's online state is just the set of edges purchased so far. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One online update. Only the current request and earlier purchases are used. -/
noncomputable def greedyStep (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) : Finset (Sym2 V) :=
  B ∪ shortestPathEdges G c B s t h

/-- Process requests in arrival order, starting from the empty purchased set. -/
noncomputable def greedy (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (initial : Finset (Sym2 V) := ∅) : Finset (Sym2 V) :=
  match requests with
  | [] => initial
  | q :: qs => greedy G c qs (fun r hr => feasible r (by simp [hr]))
      (greedyStep G c initial q.1 q.2 (feasible q (by simp)))

/-- The actual total original edge cost purchased by the implementation. -/
noncomputable def greedyCost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℝ :=
  edgeCost c (greedy G c requests feasible)

@[simp] theorem greedy_nil (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (h : ∀ q ∈ ([] : List (V × V)), G.Reachable q.1 q.2) (B : Finset (Sym2 V)) :
    greedy G c [] h B = B := rfl

theorem greedyStep_mono (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) :
    B ⊆ greedyStep G c B s t h := Finset.subset_union_left

/-- Payments are incremental costs, rather than repeated original path costs. -/
theorem greedyStep_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) :
    edgeCost c (greedyStep G c B s t h) = edgeCost c B +
      residualCost c B (shortestPathEdges G c B s t h) :=
  edgeCost_union c B _

end OnlineSteinerForest
