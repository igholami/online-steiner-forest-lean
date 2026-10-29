import OnlineSteinerForest.LowerBound.Probability.WeightedUnion
import Mathlib.Tactic.Ring
import OnlineSteinerForest.LowerBound.Probability.FactorialRatio

/-! Normalized uniform-permutation probabilities for prescribed endpoint tuples. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α I : Type*} [Fintype α] [Nonempty α] [Fintype I] {r : ℕ}

/-- Prescribing a short injective tuple costs at most `2/N^r` in uniform probability. -/
theorem prescribed_probability_le (a b : Fin r ↪ α) (hr : r ^ 2 ≤ Fintype.card α) :
    (∑ σ : Equiv.Perm α, indicator (fun σ => ∀ i, σ (a i) = b i) σ) /
      Fintype.card (Equiv.Perm α) ≤ 2 / (Fintype.card α : ℝ) ^ r := by
  rw [sum_indicator_prescribed, Fintype.card_perm]
  exact factorial_ratio_le _ _ Fintype.card_pos hr

/-- A weighted finite cover can be normalized after counting its permutation fibers. -/
theorem prescribed_cover_probability_le (P : Equiv.Perm α → Prop)
    (a b : I → Fin r ↪ α) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ σ, P σ → ∃ p, (∀ i, σ (a p i) = b p i) ∧ 1 ≤ w p)
    (hr : r ^ 2 ≤ Fintype.card α) :
    (∑ σ : Equiv.Perm α, indicator P σ) / Fintype.card (Equiv.Perm α) ≤
      2 / (Fintype.card α : ℝ) ^ r * ∑ p : I, w p := by
  have hden : (0 : ℝ) ≤ Fintype.card (Equiv.Perm α) := Nat.cast_nonneg _
  have hsum : (0 : ℝ) ≤ ∑ p : I, w p := Finset.sum_nonneg (fun p _ => hw p)
  calc
    _ ≤ ((Fintype.card α - r).factorial * ∑ p : I, w p) /
        Fintype.card (Equiv.Perm α) :=
      div_le_div_of_nonneg_right (prescribed_image_union_bound P a b w hw hcover) hden
    _ = (((Fintype.card α - r).factorial : ℝ) / (Fintype.card α).factorial) *
        ∑ p : I, w p := by rw [Fintype.card_perm]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (factorial_ratio_le _ _ Fintype.card_pos hr) hsum

end OnlineSteinerForest.LowerBound.Probability
