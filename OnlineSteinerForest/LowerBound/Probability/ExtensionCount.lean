import OnlineSteinerForest.LowerBound.Probability.Extensions

/-! Count all completions of prescribed bijective images. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α : Type*} [Fintype α]

theorem card_extensions (s t : Set α) (e : s ≃ t) :
    Fintype.card {σ : Equiv.Perm α // Extends s t e σ} =
      (Fintype.card α - Fintype.card s).factorial := by
  have hc : Fintype.card (sᶜ : Set α) = Fintype.card (tᶜ : Set α) := by
    rw [Fintype.card_compl_set, Fintype.card_compl_set, Fintype.card_congr e]
  rw [Fintype.card_congr (extensionsEquiv s t e),
    Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_compl_set]

end OnlineSteinerForest.LowerBound.Probability
