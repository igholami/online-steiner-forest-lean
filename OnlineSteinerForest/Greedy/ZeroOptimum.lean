import OnlineSteinerForest.Greedy.BasicBounds
import OnlineSteinerForest.Graph.Nonnegative

/-! The zero-optimum case of the upper theorem follows from the checked basic bounds. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem greedyCost_eq_zero_of_optimum_eq_zero (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (ho : optimum G c requests feasible = 0) : greedyCost G c requests feasible = 0 := by
  apply le_antisymm
  · simpa only [ho, mul_zero] using greedyCost_le_length_mul_optimum G c hc requests feasible
  · exact greedyCost_nonneg G c hc requests feasible

end OnlineSteinerForest
