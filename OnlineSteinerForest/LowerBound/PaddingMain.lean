import OnlineSteinerForest.LowerBound.PaddingRun
import OnlineSteinerForest.LowerBound.PaddingRatio
import OnlineSteinerForest.LowerBound.Family
import OnlineSteinerForest.LowerBound.RelabelInstance

/-! The manuscript's padding corollary: every sufficiently large exact request count. -/
namespace OnlineSteinerForest

/-- Every sufficiently large exact number of requests admits the lower bound,
for any choice of minimum residual-cost paths. -/
theorem greedy_lower_bound_exact_count :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ K : ℕ, ∀ selection : PathSelection.{0},
      letI : PathSelection.{0} := selection
      ∀ k : ℕ, K ≤ k →
      ∃ (n : ℕ) (G : SimpleGraph (Fin n)) (c : Sym2 (Fin n) → ℝ)
        (requests : List (Fin n × Fin n))
        (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
        (∀ e ∈ G.edgeSet, 0 < c e) ∧ requests.length = k ∧
        0 < optimum G c requests feasible ∧
        c₀ * optimum G c requests feasible * Real.log k * Real.log (Real.log k) ≤
          greedyCost G c requests feasible := by
  refine ⟨LowerBound.lowerConstant / 4, div_pos LowerBound.lowerConstant_pos.{0} (by norm_num),
    LowerBound.vertexCount 32, ?_⟩
  intro selection
  letI : PathSelection.{0} := selection
  intro k hk
  obtain ⟨h, hh, hlow, hupper⟩ := LowerBound.exists_padding_level k hk
  obtain ⟨σ, hσ⟩ := LowerBound.exists_retaining_matching h hh
  let e := LowerBound.vertexLabels (LowerBound.matchingSize h)
  let G := LowerBound.relabelInstanceGraph h σ e
  let c := relabelCost e (LowerBound.constructionCost (LowerBound.rankPrice h))
  let rs := LowerBound.relabelInstanceRequests h σ e
  have hf : ∀ q ∈ rs, G.Reachable q.1 q.2 := LowerBound.relabelInstance_feasible h σ e
  have hlen : rs.length ≤ k := by
    rw [LowerBound.relabelInstance_requests_length]
    exact (LowerBound.instance_requests_le_vertexCount h σ).trans hlow
  let v := e (Sum.inl ⟨0, by rw [LowerBound.twice_matchingSize];
                             exact LowerBound.vertexCount_pos h⟩)
  let ps := LowerBound.paddedRequests rs v (k - rs.length)
  have hpf : ∀ q ∈ ps, G.Reachable q.1 q.2 :=
    LowerBound.padded_feasible G rs hf v (k - rs.length)
  have hopt : optimum G c ps hpf = optimum G c rs hf :=
    LowerBound.optimum_padded G c rs hf v (k - rs.length)
  have hgreedy : greedyCost G c ps hpf = greedyCost G c rs hf := by
    unfold greedyCost
    rw [LowerBound.greedy_padded]
  refine ⟨_, G, c, ps, hpf, LowerBound.relabelInstance_positive h σ e, ?_, ?_, ?_⟩
  · simp only [ps, LowerBound.paddedRequests, List.length_append, List.length_replicate]
    omega
  · rw [hopt, LowerBound.relabelInstance_optimum_eq]
    exact LowerBound.instance_optimum_pos h hh σ hσ
  · rw [hopt, hgreedy, LowerBound.relabelInstance_optimum_eq,
      LowerBound.relabelInstance_greedy_cost h σ e]
    have ht := LowerBound.instance_padding_ratio k h hh hk hupper σ hσ
    rwa [LowerBound.instance_greedy_cost] at ht

end OnlineSteinerForest
