import OnlineSteinerForest.UpperBound.ReferenceRetained
import OnlineSteinerForest.UpperBound.ReferenceUpperReduction
import OnlineSteinerForest.Greedy.ZeroOptimum
import OnlineSteinerForest.TheoremStatements

/-! The manuscript's upper bound for the implemented greedy algorithm on standard finite graphs. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

/-- The same explicit absolute constant works for every minimum-path tie rule. -/
theorem greedy_upper_bound_explicit {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (hk : 1 ≤ requests.length) :
    greedyCost G c requests feasible ≤
      UpperBound.finalUpperConstant * optimum G c requests feasible * Real.log (2 * requests.length) *
        Real.log (Real.log (4 * requests.length)) := by
  have hc₀ : ∀ e ∈ G.edgeSet, 0 ≤ c e := fun e he => (hc e he).le
  by_cases ho : optimum G c requests feasible = 0
  · rw [greedyCost_eq_zero_of_optimum_eq_zero G c hc₀ requests feasible ho, ho]
    simp
  · have hopt : 0 < optimum G c requests feasible :=
      lt_of_le_of_ne (optimum_nonneg G c hc₀ requests feasible) (Ne.symm ho)
    have hkpos : 0 < requests.length := by omega
    let fallback : V := (requests[0]'(by omega)).1
    exact UpperBound.upper_from_retained_estimates G c hc requests feasible fallback hkpos hopt
      (fun r b hb => UpperBound.class_retained_count_bound G c hc requests feasible fallback
        hkpos hopt r b hb)

/-- Greedy costs at most an absolute constant times `OPT * log(2k) * log(log(4k))`. -/
theorem greedy_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n))
      (c : Sym2 (Fin n) → ℝ) (requests : List (Fin n × Fin n))
      (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
      (∀ e ∈ G.edgeSet, 0 < c e) → 1 ≤ requests.length →
      greedyCost G c requests feasible ≤
        C * optimum G c requests feasible * Real.log (2 * requests.length) *
          Real.log (Real.log (4 * requests.length)) := by
  refine ⟨UpperBound.finalUpperConstant, UpperBound.finalUpperConstant_pos, ?_⟩
  intro n G c requests feasible hc hk
  exact greedy_upper_bound_explicit G c requests feasible hc hk

omit [PathSelection] in
/-- One absolute constant bounds every supplied minimum-path selection rule. -/
theorem greedy_upper_bound_all_selections :
    ∃ C : ℝ, 0 < C ∧ ∀ (selection : PathSelection.{0}) (n : ℕ) (G : SimpleGraph (Fin n))
      (c : Sym2 (Fin n) → ℝ) (requests : List (Fin n × Fin n))
      (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2),
      (∀ e ∈ G.edgeSet, 0 < c e) → 1 ≤ requests.length →
      @greedyCost selection (Fin n) _ _ G c requests feasible ≤
        C * optimum G c requests feasible * Real.log (2 * requests.length) *
          Real.log (Real.log (4 * requests.length)) := by
  refine ⟨UpperBound.finalUpperConstant, UpperBound.finalUpperConstant_pos, ?_⟩
  intro selection n G c requests feasible hc hk
  letI : PathSelection.{0} := selection
  exact greedy_upper_bound_explicit G c requests feasible hc hk

/-- The exact upper-bound proposition specified before the supporting development. -/
theorem upperBoundStatement : UpperBoundStatement := greedy_upper_bound

end OnlineSteinerForest
