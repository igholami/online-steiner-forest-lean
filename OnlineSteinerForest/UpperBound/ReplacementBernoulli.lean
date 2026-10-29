import OnlineSteinerForest.Graph.Cost
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Linarith

/-! Finite Bernoulli averaging for the replacement skeleton's centers.
All expectations are finite weighted sums over functions to `Bool`. -/
namespace OnlineSteinerForest.UpperBound

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def coinWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def bernoulliWeight (p : ℝ) (x : V → Bool) : ℝ :=
  ∏ v, coinWeight p (x v)

omit [DecidableEq V] in
theorem bernoulliWeight_nonneg (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (x : V → Bool) :
    0 ≤ bernoulliWeight p x := by
  apply Finset.prod_nonneg
  intro v _
  unfold coinWeight
  split_ifs
  · exact hp
  · linarith

@[simp] theorem sum_bernoulliWeight (p : ℝ) : (∑ x : V → Bool, bernoulliWeight p x) = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_sum]
  simp [coinWeight]

/-- Prescribing the same Boolean outcome on `A` has the product probability. -/
theorem bernoulli_prescribed (p : ℝ) (A : Finset V) (b : Bool) :
    (∑ x : V → Bool, bernoulliWeight p x *
      (if ∀ v ∈ A, x v = b then 1 else 0)) = coinWeight p b ^ A.card := by
  classical
  let f := fun (v : V) (c : Bool) =>
    if v ∈ A then (if c = b then coinWeight p c else 0) else coinWeight p c
  have hfactor (x : V → Bool) : bernoulliWeight p x *
      (if ∀ v ∈ A, x v = b then 1 else 0) = ∏ v, f v (x v) := by
    split_ifs with hx
    · simp only [mul_one, bernoulliWeight]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ A
      · simp [f, hv, hx v hv]
      · simp [f, hv]
    · simp only [mul_zero]
      symm
      obtain ⟨v, hv⟩ := Classical.not_forall.mp hx
      obtain ⟨hv, hvb⟩ := Classical.not_forall.mp hv
      apply Finset.prod_eq_zero (Finset.mem_univ v)
      simp [f, hv, hvb]
  simp_rw [hfactor]
  rw [← Fintype.prod_sum]
  have hsum (v : V) : (∑ c : Bool, f v c) = if v ∈ A then coinWeight p b else 1 := by
    by_cases hv : v ∈ A <;> cases b <;> simp [f, hv, coinWeight]
  simp_rw [hsum]
  rw [← Finset.prod_filter]
  have hfilter : (Finset.univ.filter fun v : V => v ∈ A) = A := by ext v; simp
  rw [hfilter, Finset.prod_const]

end OnlineSteinerForest.UpperBound
