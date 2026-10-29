import OnlineSteinerForest.LowerBound.UniformInstances
import OnlineSteinerForest.Greedy.ExecutionRealization

/-! The same lower-bound inputs defeat every independently tied greedy execution. -/
namespace OnlineSteinerForest

theorem execution_lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ K : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
        (requests : List (Fin n × Fin n))
        (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
        (∀ e ∈ G.edgeSet, 0 < c e) ∧ max K 3 ≤ requests.length ∧
        0 < optimum G c requests feasible ∧
        ∀ E : GreedyExecution G c requests,
          c₀ * optimum G c requests feasible * Real.log requests.length *
            Real.log (Real.log requests.length) ≤ edgeCost c (E.state requests.length) := by
  obtain ⟨c₀, hc₀, hfamily⟩ := greedy_lower_bound_same_instances
  refine ⟨c₀, hc₀, ?_⟩
  intro K
  obtain ⟨n, G, c, requests, feasible, hc, hk, ho, hratio⟩ := hfamily K
  refine ⟨n, G, c, requests, feasible, hc, hk, ho, ?_⟩
  intro E
  have h := hratio E.selection
  letI : PathSelection := E.selection
  have heq := E.realized hc feasible
  change greedy G c requests feasible = E.state requests.length at heq
  simpa only [greedyCost, heq] using h

end OnlineSteinerForest
