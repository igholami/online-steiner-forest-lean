import OnlineSteinerForest.UpperBound.ThresholdGadgetSeparation

/-! Earlier labelled charging edges are free in the actual greedy prefix metric. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V J : Type*} [Fintype V] [DecidableEq V]

theorem request_gadget_prior_zero (G H : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (index : J → Fin requests.length)
    (i j : ℕ) {a b : V ⊕ J}
    (_hab : (Charging.graph H (requestLeft requests index) (requestRight requests index)).Adj a b)
    (hl : requestLabel requests index s(a, b) = some j) (hji : j < i) :
    requestMetric G c requests feasible i (requestProjection requests index a) (requestProjection requests index b) = 0 := by
  have hbase : ∀ k : J, (index k).val < i → requestMetric G c requests feasible i
      (requestLeft requests index k) (requestRight requests index k) = 0 := by
    intro k hk
    exact requestMetric_prior_zero G c hc requests feasible (index k) i hk
  cases a with
  | inl u =>
    cases b with
    | inl v => simp [requestLabel, Charging.edgeLabel] at hl
    | inr k =>
      obtain ⟨rfl, rfl⟩ := requestLabel_mixed_some requests index u k j hl
      change requestMetric G c requests feasible i (requestRight requests index k) (requestLeft requests index k) = 0
      rw [requestMetric_symm]
      exact hbase k hji
  | inr k =>
    cases b with
    | inl u =>
      have hl' : requestLabel requests index s(Sum.inl u, Sum.inr k) = some j := by
        simpa only [Sym2.eq_swap] using hl
      obtain ⟨rfl, rfl⟩ := requestLabel_mixed_some requests index u k j hl'
      exact hbase k hji
    | inr l => simp [requestLabel, Charging.edgeLabel] at hl

end OnlineSteinerForest.UpperBound
