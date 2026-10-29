import OnlineSteinerForest.LowerBound.Probability.ExtensionCount

/-! A uniform permutation hits any prescribed injective tuple equally often. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α : Type*} [Fintype α] {r : ℕ}

noncomputable def rangeEquiv (a b : Fin r ↪ α) : Set.range a ≃ Set.range b :=
  (Equiv.ofInjective a a.injective).symm.trans (Equiv.ofInjective b b.injective)

omit [Fintype α] in
@[simp] theorem rangeEquiv_apply (a b : Fin r ↪ α) (i : Fin r) :
    (rangeEquiv a b ((Equiv.ofInjective a a.injective) i) : α) = b i := by
  simp [rangeEquiv]

omit [Fintype α] in
theorem extends_range_iff (a b : Fin r ↪ α) (σ : Equiv.Perm α) :
    Extends (Set.range a) (Set.range b) (rangeEquiv a b) σ ↔ ∀ i, σ (a i) = b i := by
  constructor
  · intro hh i
    have hx := hh ((Equiv.ofInjective a a.injective) i)
    rw [rangeEquiv_apply] at hx
    change σ (a i) = b i at hx
    exact hx
  · intro hh x
    obtain ⟨i, hi⟩ := x.prop
    have hx : x = (Equiv.ofInjective a a.injective) i := Subtype.ext hi.symm
    rw [hx, rangeEquiv_apply]
    exact hh i

/-- Fixing `r` distinct images leaves exactly `(N-r)!` possible permutations. -/
theorem card_prescribed_images (a b : Fin r ↪ α) :
    Fintype.card {σ : Equiv.Perm α // ∀ i, σ (a i) = b i} =
      (Fintype.card α - r).factorial := by
  let e := Equiv.subtypeEquivRight (fun σ => (extends_range_iff a b σ).symm)
  rw [Fintype.card_congr e, card_extensions]
  simp only [Fintype.card_range, Fintype.card_fin]

end OnlineSteinerForest.LowerBound.Probability
