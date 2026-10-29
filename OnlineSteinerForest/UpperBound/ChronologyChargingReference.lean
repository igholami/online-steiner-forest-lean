import OnlineSteinerForest.UpperBound.ChronologyChargingAux
import OnlineSteinerForest.UpperBound.ChargingReference

/-! Only ordinary base edges contribute metric length in the two-spoke graph. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {W J : Type*} [DecidableEq W]

theorem charging_reference_metric (H : SimpleGraph W) (left right : J → W) (time : J → ℕ)
    (c : Sym2 W → ℝ) (d : ℕ → W → W → ENNReal) (hrefl : ∀ i w, d i w w = 0)
    (href : ∀ i {u v}, H.Adj u v → d i u v ≤ ENNReal.ofReal (c s(u, v)))
    (i : ℕ) {a b : W ⊕ J} (hab : (Charging.graph H left right).Adj a b)
    (hl : (Charging.edgeLabel right s(a, b)).map time = none) :
    d i (Charging.projection left a) (Charging.projection left b) ≤
      ENNReal.ofReal (Charging.cost c s(a, b)) := by
  cases a with
  | inl u =>
    cases b with
    | inl v => exact href i hab
    | inr j =>
      have hne : u ≠ right j := by intro h; simp [Charging.edgeLabel, h] at hl
      have hu : u = left j := (show u = _ ∨ u = _ from hab).resolve_right hne
      subst u
      change d i (left j) (left j) ≤ _
      rw [hrefl]
      exact bot_le
  | inr j =>
    cases b with
    | inl u =>
      have hne : u ≠ right j := by intro h; simp [Charging.edgeLabel, h] at hl
      have hu : u = left j := (show u = _ ∨ u = _ from hab).resolve_right hne
      subst u
      change d i (left j) (left j) ≤ _
      rw [hrefl]
      exact bot_le
    | inr k => exact hab.elim

theorem charging_timed_reference_acyclic (H : SimpleGraph W) (hH : H.IsAcyclic)
    (left right : J → W) (hne : ∀ j, left j ≠ right j) (time : J → ℕ) :
    ((Charging.graph H left right).deleteEdges {e | (Charging.edgeLabel right e).map time ≠ none}).IsAcyclic := by
  have heq : {e | (Charging.edgeLabel right e).map time ≠ none} =
      {e | Charging.edgeLabel right e ≠ none} := by ext e; simp
  rw [heq, Charging.reference_delete_eq H left right hne]
  exact Charging.referenceSpokes_acyclic H hH left

end OnlineSteinerForest.UpperBound
