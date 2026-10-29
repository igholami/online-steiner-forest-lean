import OnlineSteinerForest.Graph.Optimum
import OnlineSteinerForest.Greedy.Feasibility

/-! Nonnegative input costs imply nonnegative actual optimum and greedy costs. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem optimum_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    0 ≤ optimum G c requests feasible := by
  apply Finset.sum_nonneg
  intro e he
  exact hc e ((optimalEdges_feasible G c requests feasible).1 e he)

theorem greedyCost_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    0 ≤ greedyCost G c requests feasible := by
  apply Finset.sum_nonneg
  intro e he
  exact hc e ((greedy_feasible G c requests feasible).1 e he)

end OnlineSteinerForest
