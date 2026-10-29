import OnlineSteinerForest.Greedy.ExecutionSelection
import OnlineSteinerForest.Greedy.Algorithm

/-! A selector reproducing each observed update reproduces the whole execution. -/
namespace OnlineSteinerForest

variable {V : Type*} [Fintype V] [DecidableEq V]
variable [PathSelection]

/-- Induction over a finite sequence with an arbitrary prescribed state trajectory. -/
theorem greedy_eq_trajectory (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (state : ℕ → Finset (Sym2 V))
    (hstep : ∀ i : Fin requests.length,
      greedyStep G c (state i.val) requests[i.val].1 requests[i.val].2
        (feasible _ (List.getElem_mem i.isLt)) = state (i.val + 1)) :
    greedy G c requests feasible (state 0) = state requests.length := by
  induction requests generalizing state with
  | nil => rfl
  | cons q qs ih =>
    have hhead := hstep ⟨0, by simp⟩
    change greedyStep G c (state 0) q.1 q.2 _ = state 1 at hhead
    rw [greedy.eq_def]
    dsimp only
    rw [hhead]
    have htail : ∀ i : Fin qs.length,
        greedyStep G c (state (i.val + 1)) qs[i.val].1 qs[i.val].2
          (feasible _ (by simp only [List.mem_cons]; exact Or.inr (List.getElem_mem i.isLt))) =
            state (i.val + 1 + 1) := by
      intro i
      simpa only [List.getElem_cons_succ] using hstep ⟨i.val + 1, by simpa using Nat.succ_lt_succ i.isLt⟩
    exact ih (fun r hr => feasible r (by simp [hr])) (fun i => state (i + 1)) htail

namespace GreedyExecution

/-- Agreement on the execution's finite query table suffices; no tie agreement elsewhere is needed. -/
theorem greedy_eq_execution {G : SimpleGraph V} {c : Sym2 V → ℝ}
    {requests : List (V × V)} (E : GreedyExecution G c requests)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e)
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hselect : ∀ i : Fin requests.length,
      shortestPathEdges G c (E.state i.val) requests[i.val].1 requests[i.val].2
        (feasible _ (List.getElem_mem i.isLt)) =
      E.select (E.state i.val) requests[i.val].1 requests[i.val].2
        (feasible _ (List.getElem_mem i.isLt))) :
    greedy G c requests feasible = E.state requests.length := by
  have h := greedy_eq_trajectory G c requests feasible E.state (fun i => by
    unfold greedyStep
    rw [hselect i]
    exact E.select_successor hc i _)
  rwa [E.initial] at h

end GreedyExecution
end OnlineSteinerForest
