import OnlineSteinerForest.LowerBound.Main

/-! A single lower-bound constant works for every shortest-path tie rule. -/
namespace OnlineSteinerForest

/-- The lower bound with the same explicit constant for every supplied selector. -/
theorem greedy_lower_bound_explicit [PathSelection.{0}] :
    ∀ K : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
        (requests : List (Fin n × Fin n))
        (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
        (∀ e ∈ G.edgeSet, 0 < c e) ∧
        max K 3 ≤ requests.length ∧ 0 < optimum G c requests feasible ∧
        LowerBound.lowerConstant * optimum G c requests feasible * Real.log requests.length *
            Real.log (Real.log requests.length) ≤ greedyCost G c requests feasible := by
  intro K
  obtain ⟨h, hh, σ, hσ, hlength, hopt, hratio⟩ := LowerBound.exists_large_lower_instance K
  let e := LowerBound.vertexLabels (LowerBound.matchingSize h)
  refine ⟨Fintype.card (LowerBound.Vertex (LowerBound.matchingSize h)),
    LowerBound.relabelInstanceGraph h σ e,
    relabelCost e (LowerBound.constructionCost (LowerBound.rankPrice h)),
    LowerBound.relabelInstanceRequests h σ e,
    LowerBound.relabelInstance_feasible h σ e,
    LowerBound.relabelInstance_positive h σ e, ?_, ?_, ?_⟩
  · rwa [LowerBound.relabelInstance_requests_length]
  · rwa [LowerBound.relabelInstance_optimum_eq]
  · rw [LowerBound.relabelInstance_requests_length, LowerBound.relabelInstance_optimum_eq,
      LowerBound.relabelInstance_greedy_cost h σ e]
    rwa [LowerBound.instance_greedy_cost] at hratio

/-- Uniformity of the positive constant over all shortest-path selections. -/
theorem greedy_lower_bound_all_selections :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ selection : PathSelection.{0},
      letI : PathSelection.{0} := selection
      ∀ K : ℕ,
        ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
          (requests : List (Fin n × Fin n))
          (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
          (∀ e ∈ G.edgeSet, 0 < c e) ∧
          max K 3 ≤ requests.length ∧ 0 < optimum G c requests feasible ∧
          c₀ * optimum G c requests feasible * Real.log requests.length *
            Real.log (Real.log requests.length) ≤ greedyCost G c requests feasible := by
  refine ⟨LowerBound.lowerConstant, LowerBound.lowerConstant_pos.{0}, ?_⟩
  intro selection
  letI : PathSelection.{0} := selection
  exact greedy_lower_bound_explicit

end OnlineSteinerForest
