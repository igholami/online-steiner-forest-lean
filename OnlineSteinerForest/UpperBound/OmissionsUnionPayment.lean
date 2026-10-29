import OnlineSteinerForest.Graph.Cost

/-! Finite union costs are bounded by the sum of their nonnegative payment costs. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

theorem sum_union_le_add {κ : Type*} [DecidableEq κ] (A B : Finset κ) (f : κ → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ A ∪ B, f x ≤ (∑ x ∈ A, f x) + ∑ x ∈ B, f x := by
  have heq : A ∪ B = A ∪ (B \ A) := by ext x; simp
  rw [heq, Finset.sum_union disjoint_sdiff_self_right]
  exact add_le_add le_rfl (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun x _ _ => hf x))

theorem sum_biUnion_le_sum {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (S : Finset ι) (F : ι → Finset κ) (f : κ → ℝ)
    (hf : ∀ x, 0 ≤ f x) : (∑ x ∈ S.biUnion F, f x) ≤ ∑ i ∈ S, ∑ x ∈ F i, f x := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le_add _ _ f hf).trans (add_le_add le_rfl ih)

end OnlineSteinerForest.UpperBound
