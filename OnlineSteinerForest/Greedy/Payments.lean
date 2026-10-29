import OnlineSteinerForest.Greedy.Algorithm
import Mathlib.Tactic.Linarith

/-! Payment accounting for the implemented execution. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum of incremental payments made by exactly the same recursion as `greedy`. -/
noncomputable def payments (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (initial : Finset (Sym2 V) := ∅) : ℝ :=
  match requests with
  | [] => 0
  | q :: qs => residualCost c initial
      (shortestPathEdges G c initial q.1 q.2 (feasible q (by simp))) +
      payments G c qs (fun r hr => feasible r (by simp [hr]))
        (greedyStep G c initial q.1 q.2 (feasible q (by simp)))

/-- The manuscript's `ALG = sum_i payment_i = cost(bought edges)`. -/
theorem payments_eq_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (B : Finset (Sym2 V)) :
    edgeCost c (greedy G c requests feasible B) = edgeCost c B +
      payments G c requests feasible B := by
  induction requests generalizing B with
  | nil => simp [greedy, payments]
  | cons q qs ih =>
    simp only [greedy, payments]
    rw [ih, greedyStep_cost]
    exact add_assoc _ _ _

theorem greedyCost_eq_payments (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    greedyCost G c requests feasible = payments G c requests feasible := by
  simpa [greedyCost, edgeCost] using payments_eq_cost G c requests feasible ∅

end OnlineSteinerForest
