import OnlineSteinerForest.Greedy.Algorithm
import OnlineSteinerForest.Graph.Optimum

/-! Reflexive terminal pairs pad an execution without changing purchases or OPT. -/
namespace OnlineSteinerForest.LowerBound
variable [OnlineSteinerForest.PathSelection.{0}]

variable {V : Type} [Fintype V] [DecidableEq V]

def paddedRequests (requests : List (V × V)) (v : V) (n : ℕ) :=
  requests ++ List.replicate n (v, v)

theorem padded_feasible (G : SimpleGraph V) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (v : V) (n : ℕ) :
    ∀ q ∈ paddedRequests requests v n, G.Reachable q.1 q.2 := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact feasible q hq
  · obtain rfl := (List.mem_replicate.mp hq).2
    exact SimpleGraph.Reachable.refl _

theorem shortestPathEdges_self (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (v : V) (hv : G.Reachable v v) :
    shortestPathEdges G c B v v hv = ∅ := by
  obtain ⟨p, hp, he⟩ := (shortestPathEdges_spec G c B v v hv).1
  have hp' := SimpleGraph.Walk.isPath_iff_nil.mp hp
  cases hp'
  simpa using he.symm

theorem greedy_padded (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (v : V) (n : ℕ)
    (feasible : ∀ q ∈ paddedRequests requests v n, G.Reachable q.1 q.2)
    (B : Finset (Sym2 V)) :
    greedy G c (paddedRequests requests v n) feasible B =
      greedy G c requests (fun q hq => feasible q (List.mem_append_left _ hq)) B := by
  induction requests generalizing B with
  | nil =>
    induction n generalizing B with
    | zero => rfl
    | succ n ih =>
      simpa only [paddedRequests, List.nil_append, List.replicate_succ,
        greedy, greedyStep, shortestPathEdges_self, Finset.union_empty] using ih (padded_feasible G [] (by simp) v n) B
  | cons q qs ih =>
    simp only [paddedRequests, List.cons_append, greedy]
    exact ih _ _

theorem feasibleEdges_padded_iff (G : SimpleGraph V) (requests : List (V × V))
    (v : V) (n : ℕ) (F : Finset (Sym2 V)) :
    FeasibleEdges G (paddedRequests requests v n) F ↔ FeasibleEdges G requests F := by
  constructor
  · rintro ⟨hF, hconn⟩
    exact ⟨hF, fun q hq => hconn q (List.mem_append_left _ hq)⟩
  · rintro ⟨hF, hconn⟩
    refine ⟨hF, ?_⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hconn q hq
    · obtain rfl := (List.mem_replicate.mp hq).2
      exact SimpleGraph.Reachable.refl _

theorem optimum_padded (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (v : V) (n : ℕ) :
    optimum G c (paddedRequests requests v n) (padded_feasible G requests feasible v n) =
      optimum G c requests feasible := by
  apply le_antisymm
  · exact optimum_le _ _ _ _ _ ((feasibleEdges_padded_iff _ _ _ _ _).2
      (optimalEdges_feasible G c requests feasible))
  · exact optimum_le _ _ _ _ _ ((feasibleEdges_padded_iff _ _ _ _ _).1
      (optimalEdges_feasible G c _ _))

end OnlineSteinerForest.LowerBound
