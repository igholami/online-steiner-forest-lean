import OnlineSteinerForest.LowerBound.Probability.EmbeddingSamples
import OnlineSteinerForest.LowerBound.Probability.PermutationRestriction

/-! Product moments of samples obtained by restricting a uniform rank permutation. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α : Type*} [Fintype α] [Nonempty α] {r : ℕ}

theorem embedding_product_mean_le (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hr : r ≤ Fintype.card α) :
    (∑ b : Fin r ↪ α, ∏ j : Fin r, w (b j)) / Fintype.card (Fin r ↪ α) ≤
      ((∑ x : α, w x) / Fintype.card α) ^ r := by
  let e := @orderedSampleEquivEmbedding α _ r
  have hs := Fintype.sum_equiv e
    (fun q => ∏ j : Fin r, w (q.2 j).val)
    (fun b : Fin r ↪ α => ∏ j : Fin r, w (b j)) (fun _ => rfl)
  have hc := Fintype.card_congr e
  rw [← hs, ← hc]
  simpa only [Finset.card_univ] using Sampling.ordered_sampling_without_replacement
    (Finset.univ : Finset α) r w (fun x _ => hw x) Finset.univ_nonempty
      (by simpa only [Finset.card_univ] using hr)

/-- Distinct traversed edges receive a uniform sample of distinct ranks. -/
theorem permutation_product_mean_le (a : Fin r ↪ α) (w : α → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ σ : Equiv.Perm α, ∏ j : Fin r, w (σ (a j))) / Fintype.card (Equiv.Perm α) ≤
      ((∑ x : α, w x) / Fintype.card α) ^ r := by
  have hr : r ≤ Fintype.card α := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding a
  change (∑ σ : Equiv.Perm α, (fun b : Fin r ↪ α => ∏ j, w (b j)) (restrict a σ)) /
    Fintype.card (Equiv.Perm α) ≤ _
  exact (average_permutation_restrict a (fun b : Fin r ↪ α => ∏ j, w (b j))).trans_le
    (embedding_product_mean_le w hw hr)

/-- Unnormalized form for the sum over all distinct ordered rank assignments. -/
theorem sum_embedding_products_le (w : α → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hr : r ≤ Fintype.card α) :
    (∑ b : Fin r ↪ α, ∏ j : Fin r, w (b j)) ≤
      (Fintype.card α).descFactorial r * ((∑ x : α, w x) / Fintype.card α) ^ r := by
  have hc : 0 < Fintype.card (Fin r ↪ α) := by
    rw [Fintype.card_embedding_eq, Fintype.card_fin]
    exact Nat.descFactorial_pos.mpr hr
  have hh := (div_le_iff₀ (Nat.cast_pos.mpr hc : (0 : ℝ) < Fintype.card (Fin r ↪ α))).mp
    (embedding_product_mean_le w hw hr)
  simpa only [Fintype.card_embedding_eq, Fintype.card_fin, mul_comm] using hh

end OnlineSteinerForest.LowerBound.Probability
