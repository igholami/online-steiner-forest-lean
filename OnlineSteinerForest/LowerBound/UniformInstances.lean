import OnlineSteinerForest.LowerBound.SelectionInvariant
import OnlineSteinerForest.LowerBound.Family

/-! A single family of inputs defeats every shortest-path tie rule. -/
namespace OnlineSteinerForest

/-- The instance and the lower-bound constant are chosen before the tie rule. -/
theorem greedy_lower_bound_same_instances :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ K : ℕ,
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
        (requests : List (Fin n × Fin n))
        (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
        (∀ e ∈ G.edgeSet, 0 < c e) ∧ max K 3 ≤ requests.length ∧
        0 < optimum G c requests feasible ∧
        ∀ selection : PathSelection.{0},
          letI : PathSelection.{0} := selection
          c₀ * optimum G c requests feasible * Real.log requests.length *
            Real.log (Real.log requests.length) ≤ greedyCost G c requests feasible := by
  let p : PathSelection.{0} := canonicalPathSelection.{0}
  letI : PathSelection.{0} := p
  refine ⟨LowerBound.lowerConstant, LowerBound.lowerConstant_pos.{0}, ?_⟩
  intro K
  obtain ⟨h, hh, σ, hσ, hlength, hopt, hratio⟩ := LowerBound.exists_large_lower_instance K
  let e := LowerBound.vertexLabels (LowerBound.matchingSize h)
  have hratio' : LowerBound.lowerConstant *
      optimum (LowerBound.relabelInstanceGraph h σ e)
        (relabelCost e (LowerBound.constructionCost (LowerBound.rankPrice h)))
        (LowerBound.relabelInstanceRequests h σ e) (LowerBound.relabelInstance_feasible h σ e) *
        Real.log (LowerBound.relabelInstanceRequests h σ e).length *
        Real.log (Real.log (LowerBound.relabelInstanceRequests h σ e).length) ≤
      ∑ i ∈ LowerBound.retainedRanks h σ, LowerBound.rankPrice h i := by
    rw [LowerBound.relabelInstance_requests_length, LowerBound.relabelInstance_optimum_eq]
    rwa [LowerBound.instance_greedy_cost] at hratio
  refine ⟨_, LowerBound.relabelInstanceGraph h σ e,
    relabelCost e (LowerBound.constructionCost (LowerBound.rankPrice h)),
    LowerBound.relabelInstanceRequests h σ e, LowerBound.relabelInstance_feasible h σ e,
    LowerBound.relabelInstance_positive h σ e, ?_, ?_, ?_⟩
  · rwa [LowerBound.relabelInstance_requests_length]
  · rwa [LowerBound.relabelInstance_optimum_eq]
  · intro selection
    letI : PathSelection.{0} := selection
    have hg := LowerBound.relabelInstance_greedy_cost h σ e
    have hG := LowerBound.relabelInstanceGraph_selection_eq p selection h σ e
    have hR := LowerBound.relabelInstanceRequests_selection_eq p selection h σ e
    have hcost :
        greedyCost (letI := p; LowerBound.relabelInstanceGraph h σ e)
          (relabelCost e (LowerBound.constructionCost (LowerBound.rankPrice h)))
          (letI := p; LowerBound.relabelInstanceRequests h σ e)
          (letI := p; LowerBound.relabelInstance_feasible h σ e) =
        ∑ i ∈ (letI := p; LowerBound.retainedRanks h σ), LowerBound.rankPrice h i := by
      have heq := LowerBound.greedyCost_input_eq
        (c := relabelCost e (LowerBound.constructionCost (LowerBound.rankPrice h))) hG hR
        (letI := p; LowerBound.relabelInstance_feasible h σ e)
        (LowerBound.relabelInstance_feasible h σ e)
      have htotal := heq.trans hg
      rwa [LowerBound.retainedRanks_selection_eq selection p] at htotal
    rw [hcost]
    exact hratio'

end OnlineSteinerForest
