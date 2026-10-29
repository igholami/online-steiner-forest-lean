import OnlineSteinerForest.UpperBound.ThresholdRequestGadget
import OnlineSteinerForest.UpperBound.ThresholdGreedyMetric

/-! Every labelled charging edge has the implemented request's pre-purchase separation. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V J : Type*} [Fintype V] [DecidableEq V]

theorem requestLabel_mixed_some (requests : List (V × V)) (index : J → Fin requests.length)
    (u : V) (j : J) (i : ℕ)
    (hl : requestLabel requests index s(Sum.inl u, Sum.inr j) = some i) :
    u = requestRight requests index j ∧ (index j).val = i := by
  by_cases hu : u = requestRight requests index j
  · exact ⟨hu, by simpa [requestLabel, Charging.edgeLabel, hu] using hl⟩
  · simp [requestLabel, Charging.edgeLabel, hu] at hl

theorem request_gadget_separation (G H : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (index : J → Fin requests.length) (τ : ℝ)
    (hpay : ∀ j, τ ≤ payment G c requests feasible (index j))
    {a b : V ⊕ J} (_hab : (Charging.graph H (requestLeft requests index) (requestRight requests index)).Adj a b)
    (i : ℕ) (hl : requestLabel requests index s(a, b) = some i) :
    ENNReal.ofReal τ ≤ requestMetric G c requests feasible i
      (requestProjection requests index a) (requestProjection requests index b) := by
  have hbase : ∀ j : J, ENNReal.ofReal τ ≤ requestMetric G c requests feasible (index j).val
      (requestLeft requests index j) (requestRight requests index j) := by
    intro j
    rw [show requestMetric G c requests feasible (index j).val
      (requestLeft requests index j) (requestRight requests index j) =
        ENNReal.ofReal (payment G c requests feasible (index j)) from requestMetric_payment G c requests feasible (index j)]
    exact ENNReal.ofReal_le_ofReal (hpay j)
  cases a with
  | inl u =>
    cases b with
    | inl v => simp [requestLabel, Charging.edgeLabel] at hl
    | inr j =>
      obtain ⟨rfl, rfl⟩ := requestLabel_mixed_some requests index u j i hl
      change ENNReal.ofReal τ ≤ requestMetric G c requests feasible (index j).val
        (requestRight requests index j) (requestLeft requests index j)
      rw [requestMetric_symm]
      exact hbase j
  | inr j =>
    cases b with
    | inl u =>
      have hl' : requestLabel requests index s(Sum.inl u, Sum.inr j) = some i := by
        simpa only [Sym2.eq_swap] using hl
      obtain ⟨rfl, rfl⟩ := requestLabel_mixed_some requests index u j i hl'
      exact hbase j
    | inr k => simp [requestLabel, Charging.edgeLabel] at hl

end OnlineSteinerForest.UpperBound
