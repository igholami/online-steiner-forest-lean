import OnlineSteinerForest.UpperBound.ChargingLabels
import OnlineSteinerForest.UpperBound.ChargingComponents
import OnlineSteinerForest.UpperBound.GirthResidualDistance

/-! The two-spoke construction transfers actual pair separation and prior-zero metrics. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {W X J : Type*} [DecidableEq W]

theorem charging_label_endpoints (right : J → W) (time : J → ℕ)
    (a b : W ⊕ J) (i : ℕ) (hl : (Charging.edgeLabel right s(a, b)).map time = some i) :
    ∃ j, time j = i ∧ ((a = .inr j ∧ b = .inl (right j)) ∨ (a = .inl (right j) ∧ b = .inr j)) := by
  obtain ⟨j, hj, hi⟩ := Option.map_eq_some_iff.mp hl
  have heq := Charging.edgeLabel_some right s(a, b) j hj
  exact ⟨j, hi, Sym2.eq_iff.mp heq⟩

theorem charging_pair_separation (left right : J → W) (time : J → ℕ)
    (d : ℕ → W → W → ENNReal) (hsymm : ∀ i u v, d i u v = d i v u)
    (sep : ENNReal) (hsep : ∀ j, sep ≤ d (time j) (left j) (right j))
    {a b : W ⊕ J} (i : ℕ) (hl : (Charging.edgeLabel right s(a, b)).map time = some i) :
    sep ≤ d i (Charging.projection left a) (Charging.projection left b) := by
  obtain ⟨j, rfl, hcases⟩ := charging_label_endpoints right time a b i hl
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hsep j
  · change sep ≤ d (time j) (right j) (left j)
    rw [hsymm]
    exact hsep j

theorem charging_pair_prior_zero (left right : J → W) (time : J → ℕ)
    (d : ℕ → W → W → ENNReal) (hsymm : ∀ i u v, d i u v = d i v u)
    (hprior : ∀ i j, time j < i → d i (left j) (right j) = 0)
    (i j : ℕ) {a b : W ⊕ J} (hl : (Charging.edgeLabel right s(a, b)).map time = some j) (hji : j < i) :
    d i (Charging.projection left a) (Charging.projection left b) = 0 := by
  obtain ⟨k, rfl, hcases⟩ := charging_label_endpoints right time a b j hl
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hprior i k hji
  · change d i (right k) (left k) = 0
    rw [hsymm]
    exact hprior i k hji

end OnlineSteinerForest.UpperBound
