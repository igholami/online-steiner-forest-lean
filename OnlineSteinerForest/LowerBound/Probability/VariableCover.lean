import OnlineSteinerForest.LowerBound.Probability.PrescribedProbability

/-! Weighted covers whose endpoint-tuple lengths vary with the number of shortcuts. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α I : Type*} [Fintype α] [Nonempty α] [Fintype I]

theorem variable_cover_probability_le (P : Equiv.Perm α → Prop) (r : I → ℕ)
    (a b : ∀ p, Fin (r p) ↪ α) (w : I → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hcover : ∀ σ, P σ → ∃ p, (∀ k, σ (a p k) = b p k) ∧ 1 ≤ w p)
    (hr : ∀ p, (r p) ^ 2 ≤ Fintype.card α) :
    (∑ σ : Equiv.Perm α, indicator P σ) / Fintype.card (Equiv.Perm α) ≤
      ∑ p : I, w p * (2 / (Fintype.card α : ℝ) ^ (r p)) := by
  have hden : (0 : ℝ) ≤ Fintype.card (Equiv.Perm α) := Nat.cast_nonneg _
  calc
    _ ≤ (∑ p : I, w p * ∑ σ : Equiv.Perm α,
        indicator (fun σ => ∀ k, σ (a p k) = b p k) σ) /
        Fintype.card (Equiv.Perm α) :=
      div_le_div_of_nonneg_right
        (weighted_union_bound P (fun p σ => ∀ k, σ (a p k) = b p k) w hw hcover) hden
    _ = ∑ p : I, w p * ((∑ σ : Equiv.Perm α,
        indicator (fun σ => ∀ k, σ (a p k) = b p k) σ) /
        Fintype.card (Equiv.Perm α)) := by
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ ≤ _ := Finset.sum_le_sum (fun p _ =>
      mul_le_mul_of_nonneg_left (prescribed_probability_le (a p) (b p) (hr p)) (hw p))

/-- Relaxing validity restrictions on a finite shape family only increases a nonnegative sum. -/
theorem sum_subtype_le_sum (valid : I → Prop) (f : I → ℝ) (hf : ∀ p, 0 ≤ f p) :
    (∑ p : {p // valid p}, f p.val) ≤ ∑ p : I, f p := by
  rw [← Finset.sum_subtype (Finset.univ.filter valid) (by simp) f]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => hf p)

end OnlineSteinerForest.LowerBound.Probability
