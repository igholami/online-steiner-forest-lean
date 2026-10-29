import Mathlib.Data.Fintype.Perm
import Mathlib.Logic.Equiv.Set

/-! Bijections extending a prescribed bijection are exactly bijections of the complements. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {α : Type*} (s t : Set α)

/-- Complete prescribed images on `s` with a bijection between the remaining vertices. -/
noncomputable def extend (e : s ≃ t) (f : (sᶜ : Set α) ≃ (tᶜ : Set α)) : Equiv.Perm α :=
  (Equiv.Set.sumCompl s).symm.trans ((e.sumCongr f).trans (Equiv.Set.sumCompl t))

@[simp] theorem extend_mem (e : s ≃ t) (f : (sᶜ : Set α) ≃ (tᶜ : Set α)) (x : s) :
    extend s t e f x = e x := by simp [extend]

@[simp] theorem extend_compl (e : s ≃ t) (f : (sᶜ : Set α) ≃ (tᶜ : Set α))
    (x : (sᶜ : Set α)) : extend s t e f x = f x := by simp [extend]

/-- The prescribed part of a permutation. -/
def Extends (e : s ≃ t) (σ : Equiv.Perm α) : Prop := ∀ x : s, σ x = e x

theorem extends_mem_iff (e : s ≃ t) (σ : Equiv.Perm α) (hσ : Extends s t e σ) (x : α) :
    x ∈ s ↔ σ x ∈ t := by
  constructor
  · intro hx
    rw [hσ ⟨x, hx⟩]
    exact (e ⟨x, hx⟩).prop
  · intro hx
    obtain ⟨a, ha⟩ := e.surjective ⟨σ x, hx⟩
    have heq : σ a = σ x := (hσ a).trans (congrArg Subtype.val ha)
    exact σ.injective heq ▸ a.prop

noncomputable def extensionsEquiv (e : s ≃ t) :
    {σ : Equiv.Perm α // Extends s t e σ} ≃ ((sᶜ : Set α) ≃ (tᶜ : Set α)) where
  toFun σ := σ.val.subtypeEquiv (fun x => not_congr (extends_mem_iff s t e σ.val σ.prop x))
  invFun f := ⟨extend s t e f, fun x => extend_mem s t e f x⟩
  left_inv σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x ∈ s
    · have he := extend_mem s t e
        (σ.val.subtypeEquiv (fun x => not_congr (extends_mem_iff s t e σ.val σ.prop x))) ⟨x, hx⟩
      exact he.trans (σ.prop ⟨x, hx⟩).symm
    · exact extend_compl s t e
        (σ.val.subtypeEquiv (fun x => not_congr (extends_mem_iff s t e σ.val σ.prop x))) ⟨x, hx⟩
  right_inv f := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    exact extend_compl s t e f x

end OnlineSteinerForest.LowerBound.Probability
