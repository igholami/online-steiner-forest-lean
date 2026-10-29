import OnlineSteinerForest.UpperBound.Main
import OnlineSteinerForest.LowerBound.UniformInstances

/-! Both tight bounds, stated together using the implemented greedy cost and standard mathlib graphs. -/
namespace OnlineSteinerForest

/-- The greedy online Steiner forest algorithm has ratio `O(log k * log log k)`. -/
theorem upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ selection : PathSelection.{0},
    letI : PathSelection.{0} := selection
    ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (c : Sym2 (Fin n) → ℝ) (requests : List (Fin n × Fin n))
      (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
      (∀ e ∈ G.edgeSet, 0 < c e) → 1 ≤ requests.length →
      greedyCost G c requests feasible ≤
        C * optimum G c requests feasible * Real.log (2 * requests.length) *
          Real.log (Real.log (4 * requests.length)) := greedy_upper_bound_all_selections

/-- Positive-cost instances with arbitrarily many requests attain the matching
`Omega(log k * log log k)` lower ratio for this same implemented algorithm. -/
theorem lower_bound :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ K : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
        (requests : List (Fin n × Fin n))
        (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
        (∀ e ∈ G.edgeSet, 0 < c e) ∧ max K 3 ≤ requests.length ∧
        0 < optimum G c requests feasible ∧
        ∀ selection : PathSelection.{0},
          letI : PathSelection.{0} := selection
          c₀ * optimum G c requests feasible * Real.log requests.length *
            Real.log (Real.log requests.length) ≤ greedyCost G c requests feasible := greedy_lower_bound_same_instances

end OnlineSteinerForest
