import OnlineSteinerForest.Greedy.ExecutionRealization
import OnlineSteinerForest.UpperBound.Main

/-! The upper bound holds for every independently tied minimum-path execution. -/
namespace OnlineSteinerForest

/-- One absolute constant bounds all valid executions, including arrival-dependent ties. -/
theorem execution_upper_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (hk : 1 ≤ requests.length)
    (E : GreedyExecution G c requests) :
    edgeCost c (E.state requests.length) ≤
      UpperBound.finalUpperConstant * optimum G c requests feasible *
        Real.log (2 * requests.length) * Real.log (Real.log (4 * requests.length)) := by
  letI : PathSelection := E.selection
  have h := greedy_upper_bound_explicit G c requests feasible hc hk
  have heq := E.realized hc feasible
  change greedy G c requests feasible = E.state requests.length at heq
  simpa only [greedyCost, heq] using h

end OnlineSteinerForest
