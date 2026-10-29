import OnlineSteinerForest.UpperBound.ThresholdGadgetSeparation

/-! Unlabelled charging edges are paid for by original reference-edge costs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V J : Type*} [Fintype V] [DecidableEq V]

theorem request_gadget_reference_bound (G H : SimpleGraph V) (hHG : H ≤ G)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (index : J → Fin requests.length)
    (i : ℕ) {a b : V ⊕ J}
    (hab : (Charging.graph H (requestLeft requests index) (requestRight requests index)).Adj a b)
    (hl : requestLabel requests index s(a, b) = none) :
    requestMetric G c requests feasible i (requestProjection requests index a) (requestProjection requests index b) ≤
      ENNReal.ofReal (Charging.cost (fun e => max (c e) 0) s(a, b)) := by
  cases a with
  | inl u =>
    cases b with
    | inl v =>
      change H.Adj u v at hab
      exact (residualEDistance_adj_le G c hc _ (hHG hab)).trans
        (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    | inr j =>
      have hne : u ≠ requestRight requests index j := by
        intro h
        simp [requestLabel, Charging.edgeLabel, h] at hl
      have hu : u = requestLeft requests index j := (show u = _ ∨ u = _ from hab).resolve_right hne
      subst u
      change requestMetric G c requests feasible i (requestLeft requests index j) (requestLeft requests index j) ≤ _
      rw [requestMetric_refl G c hc]
      exact bot_le
  | inr j =>
    cases b with
    | inl u =>
      have hne : u ≠ requestRight requests index j := by
        intro h
        simp [requestLabel, Charging.edgeLabel, h] at hl
      have hu : u = requestLeft requests index j := (show u = _ ∨ u = _ from hab).resolve_right hne
      subst u
      change requestMetric G c requests feasible i (requestLeft requests index j) (requestLeft requests index j) ≤ _
      rw [requestMetric_refl G c hc]
      exact bot_le
    | inr k => exact hab.elim

end OnlineSteinerForest.UpperBound
