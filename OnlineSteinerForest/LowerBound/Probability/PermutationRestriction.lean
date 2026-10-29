import OnlineSteinerForest.LowerBound.Probability.PrescribedImages
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic

/-! Uniform permutation restrictions have equal-size fibers. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α : Type*} [Fintype α] {r : ℕ}

def restrict (a : Fin r ↪ α) (σ : Equiv.Perm α) : Fin r ↪ α := a.trans σ.toEmbedding

omit [Fintype α] in
@[simp] theorem restrict_apply (a : Fin r ↪ α) (σ : Equiv.Perm α) (i : Fin r) :
    restrict a σ i = σ (a i) := rfl

omit [Fintype α] in
theorem restrict_eq_iff (a b : Fin r ↪ α) (σ : Equiv.Perm α) :
    restrict a σ = b ↔ ∀ i, σ (a i) = b i := Function.Embedding.ext_iff

theorem card_restrict_fiber (a b : Fin r ↪ α) :
    Fintype.card {σ : Equiv.Perm α // restrict a σ = b} =
      (Fintype.card α - r).factorial := by
  let e := Equiv.subtypeEquivRight (fun σ => restrict_eq_iff a b σ)
  rw [Fintype.card_congr e, card_prescribed_images]

/-- Every injective image tuple occurs the same number of times in a uniform permutation. -/
theorem sum_permutation_restrict (a : Fin r ↪ α) (f : (Fin r ↪ α) → ℝ) :
    (∑ σ : Equiv.Perm α, f (restrict a σ)) =
      (Fintype.card α - r).factorial * ∑ b : Fin r ↪ α, f b := by
  calc
    _ = ∑ b : Fin r ↪ α, ∑ σ : {σ : Equiv.Perm α // restrict a σ = b}, f (restrict a σ.val) :=
      (Fintype.sum_fiberwise (restrict a) (fun σ => f (restrict a σ))).symm
    _ = ∑ b : Fin r ↪ α, (Fintype.card α - r).factorial * f b := by
      apply Finset.sum_congr rfl
      intro b _
      have hs : (∑ σ : {σ : Equiv.Perm α // restrict a σ = b}, f (restrict a σ.val)) =
          ∑ _σ : {σ : Equiv.Perm α // restrict a σ = b}, f b := by
        apply Finset.sum_congr rfl
        intro σ _
        exact congrArg f σ.prop
      rw [hs]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_restrict_fiber]
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem permutation_card_factorization (a : Fin r ↪ α) :
    (Fintype.card (Equiv.Perm α) : ℝ) =
      (Fintype.card α - r).factorial * Fintype.card (Fin r ↪ α) := by
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    sum_permutation_restrict a (fun _ => (1 : ℝ))

/-- Consequently the normalized permutation average is the normalized tuple average. -/
theorem average_permutation_restrict (a : Fin r ↪ α) (f : (Fin r ↪ α) → ℝ) :
    (∑ σ : Equiv.Perm α, f (restrict a σ)) / Fintype.card (Equiv.Perm α) =
      (∑ b : Fin r ↪ α, f b) / Fintype.card (Fin r ↪ α) := by
  rw [sum_permutation_restrict, permutation_card_factorization a]
  exact mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne')

end OnlineSteinerForest.LowerBound.Probability
