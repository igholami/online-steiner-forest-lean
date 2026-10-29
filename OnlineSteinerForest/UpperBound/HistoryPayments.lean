import OnlineSteinerForest.UpperBound.HistoryExecution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! The prefix execution advances by the implemented update and telescopes its payments. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem boughtBefore_succ (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) :
    boughtBefore G c requests feasible (i.val + 1) =
      greedyStep G c (boughtBefore G c requests feasible i.val) requests[i.val].1 requests[i.val].2
        (feasible requests[i.val] (List.getElem_mem i.isLt)) := by
  have heq := List.take_succ_eq_append_getElem i.isLt
  have hconcat : ∀ q ∈ requests.take i.val ++ [requests[i.val]], G.Reachable q.1 q.2 := by
    intro q hq
    rw [← heq] at hq
    exact feasible q (List.mem_of_mem_take hq)
  have hreplace := greedy_congr_requests G c (requests.take (i.val + 1))
    (requests.take i.val ++ [requests[i.val]])
    (fun q hq => feasible q (List.mem_of_mem_take hq)) hconcat heq ∅
  have hcomp := greedy_append G c (requests.take i.val) [requests[i.val]] hconcat ∅
  exact hreplace.trans hcomp

theorem payment_eq_cost_increment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) :
    payment G c requests feasible i = edgeCost c (boughtBefore G c requests feasible (i.val + 1)) -
      edgeCost c (boughtBefore G c requests feasible i.val) := by
  rw [boughtBefore_succ, greedyStep_cost]
  change residualCost c _ _ = _ + residualCost c _ _ - _
  ring

theorem sum_payments_eq_greedyCost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    ∑ i : Fin requests.length, payment G c requests feasible i = greedyCost G c requests feasible := by
  let f := fun j => edgeCost c (boughtBefore G c requests feasible j)
  have htel : ∀ n, (∑ j ∈ Finset.range n, (f (j + 1) - f j)) = f n - f 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  calc
    _ = ∑ i : Fin requests.length, (f (i.val + 1) - f i.val) :=
      Finset.sum_congr rfl (fun i _ => payment_eq_cost_increment G c requests feasible i)
    _ = ∑ j ∈ Finset.range requests.length, (f (j + 1) - f j) :=
      Fin.sum_univ_eq_sum_range (fun j => f (j + 1) - f j) requests.length
    _ = _ := htel _
    _ = _ := by simp [f, greedyCost, edgeCost]

theorem payment_le_optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length) :
    payment G c requests feasible i ≤ optimum G c requests feasible := by
  have ho := optimalEdges_feasible G c requests feasible
  exact shortestPathEdges_cost_le c hc _ requests[i.val].1 requests[i.val].2 _
    (optimalEdges G c requests feasible) ho.1 (ho.2 requests[i.val] (List.getElem_mem i.isLt))

end OnlineSteinerForest.UpperBound
