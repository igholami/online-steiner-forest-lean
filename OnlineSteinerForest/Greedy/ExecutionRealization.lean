import OnlineSteinerForest.Greedy.ExecutionRun
import OnlineSteinerForest.Greedy.SelectionOverride

/-! Every finite independently tied greedy execution is realized by one valid global selector. -/
namespace OnlineSteinerForest.GreedyExecution

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {c : Sym2 V → ℝ} {requests : List (V × V)}

/-- Extend the finite query table to a selector on every finite graph. -/
noncomputable def selection (E : GreedyExecution G c requests) : PathSelection :=
  overridePathSelection G c E.select E.select_spec

/-- Realization concerns all purchased edges, rather than merely the same total cost. -/
theorem realized (E : GreedyExecution G c requests)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e)
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    letI : PathSelection := E.selection
    greedy G c requests feasible = E.state requests.length := by
  letI : PathSelection := E.selection
  apply E.greedy_eq_execution hc feasible
  intro i
  exact overridePathSelection_choose G c E.select E.select_spec _ _ _ _

end OnlineSteinerForest.GreedyExecution
