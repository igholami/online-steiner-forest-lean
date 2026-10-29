import OnlineSteinerForest.Greedy.Payments
import OnlineSteinerForest.Greedy.Feasibility
import OnlineSteinerForest.Graph.Comparison

/-! Elementary baseline bounds for the actual implementation.
The `k * OPT` bound is not the manuscript's tight upper bound. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every feasible solution, including greedy, costs at least the offline optimum. -/
theorem optimum_le_greedyCost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    optimum G c requests feasible ≤ greedyCost G c requests feasible :=
  optimum_le G c requests feasible _ (greedy_feasible G c requests feasible)

/-- Each request costs at most the cost of any fixed feasible comparison solution. -/
theorem payments_le_length_mul (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (F : Finset (Sym2 V)) (hF : FeasibleEdges G requests F)
    (B : Finset (Sym2 V)) :
    payments G c requests feasible B ≤ requests.length * edgeCost c F := by
  induction requests generalizing B with
  | nil => simp [payments]
  | cons q qs ih =>
    have hp := shortestPathEdges_cost_le c hc B q.1 q.2
      (feasible q (by simp)) F hF.1 (hF.2 q (by simp))
    have htail : FeasibleEdges G qs F :=
      ⟨hF.1, fun r hr => hF.2 r (by simp [hr])⟩
    have ht := ih (fun r hr => feasible r (by simp [hr])) htail
      (greedyStep G c B q.1 q.2 (feasible q (by simp)))
    simp only [payments, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    linarith

/-- A checked baseline competitive bound, strictly weaker than the target. -/
theorem greedyCost_le_length_mul_optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    greedyCost G c requests feasible ≤ requests.length * optimum G c requests feasible := by
  rw [greedyCost_eq_payments]
  exact payments_le_length_mul G c hc requests feasible _
    (optimalEdges_feasible G c requests feasible) ∅

/-- A one-request execution is offline optimal. -/
theorem greedyCost_eq_optimum_of_length_one (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hlen : requests.length = 1) :
    greedyCost G c requests feasible = optimum G c requests feasible := by
  apply le_antisymm
  · simpa [hlen] using greedyCost_le_length_mul_optimum G c hc requests feasible
  · exact optimum_le_greedyCost G c requests feasible

end OnlineSteinerForest
