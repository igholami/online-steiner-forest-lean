import OnlineSteinerForest.LowerBound.Probability.PrescribedImages
import OnlineSteinerForest.Graph.Cost
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.SetTheory.Cardinal.Finite

/-! Finite weighted union bounds, with prescribed-image events counted exactly. -/
namespace OnlineSteinerForest.LowerBound.Probability

open scoped Classical

variable {Ω I α : Type*} [Fintype Ω] [Fintype I] [Fintype α]

/-- A real indicator with its classical decision fixed inside the definition. -/
noncomputable def indicator (P : Ω → Prop) (ω : Ω) : ℝ := by
  classical
  exact if P ω then 1 else 0

omit [Fintype Ω] in
@[simp] theorem indicator_true (P : Ω → Prop) (ω : Ω) (h : P ω) : indicator P ω = 1 := by
  simp [indicator, h]

omit [Fintype Ω] in
@[simp] theorem indicator_false (P : Ω → Prop) (ω : Ω) (h : ¬ P ω) : indicator P ω = 0 := by
  simp [indicator, h]

omit [Fintype Ω] in
theorem indicator_nonneg (P : Ω → Prop) (ω : Ω) : 0 ≤ indicator P ω := by
  by_cases h : P ω <;> simp [indicator, h]

theorem sum_indicator_eq_card (P : Ω → Prop) :
    (∑ ω : Ω, indicator P ω) = Nat.card {ω // P ω} := by
  unfold indicator
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter]
  simp

/-- A weighted collection of witnesses bounds the indicator of any covered event. -/
theorem weighted_union_bound (P : Ω → Prop) (E : I → Ω → Prop) (w : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hcover : ∀ ω, P ω → ∃ i, E i ω ∧ 1 ≤ w i) :
    (∑ ω : Ω, indicator P ω) ≤ ∑ i : I, w i * ∑ ω : Ω, indicator (E i) ω := by
  have hpoint (ω : Ω) : indicator P ω ≤ ∑ i : I, w i * indicator (E i) ω := by
    have hnn (i : I) : 0 ≤ w i * indicator (E i) ω :=
      mul_nonneg (hw i) (indicator_nonneg _ _)
    by_cases hp : P ω
    · obtain ⟨i, hi, hwi⟩ := hcover ω hp
      rw [indicator_true P ω hp]
      calc
        _ ≤ w i := hwi
        _ = w i * indicator (E i) ω := by rw [indicator_true _ _ hi, mul_one]
        _ ≤ _ := Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
    · rw [indicator_false P ω hp]
      exact Finset.sum_nonneg (fun i _ => hnn i)
  calc
    _ ≤ ∑ ω : Ω, ∑ i : I, w i * indicator (E i) ω :=
      Finset.sum_le_sum (fun ω _ => hpoint ω)
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.mul_sum _ _ _).symm

theorem sum_indicator_prescribed {r : ℕ} (a b : Fin r ↪ α) :
    (∑ σ : Equiv.Perm α, indicator (fun σ => ∀ i, σ (a i) = b i) σ) =
      (Fintype.card α - r).factorial := by
  calc
    _ = (Nat.card {σ : Equiv.Perm α // ∀ i, σ (a i) = b i} : ℝ) :=
      sum_indicator_eq_card _
    _ = _ := by
      have hc : Nat.card {σ : Equiv.Perm α // ∀ i, σ (a i) = b i} =
          (Fintype.card α - r).factorial :=
        Nat.card_eq_fintype_card.trans (card_prescribed_images a b)
      exact congrArg (fun n : ℕ => (n : ℝ)) hc

/-- A family of injective endpoint prescriptions contributes one factorial fiber per witness. -/
theorem prescribed_image_union_bound {r : ℕ} (P : Equiv.Perm α → Prop)
    (a b : I → Fin r ↪ α) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hcover : ∀ σ, P σ → ∃ p, (∀ i, σ (a p i) = b p i) ∧ 1 ≤ w p) :
    (∑ σ : Equiv.Perm α, indicator P σ) ≤
      (Fintype.card α - r).factorial * ∑ p : I, w p := by
  calc
    _ ≤ ∑ p : I, w p * ∑ σ : Equiv.Perm α,
        indicator (fun σ => ∀ i, σ (a p i) = b p i) σ :=
      weighted_union_bound P (fun p σ => ∀ i, σ (a p i) = b p i) w hw hcover
    _ = ∑ p : I, w p * (Fintype.card α - r).factorial := by
      apply Finset.sum_congr rfl
      intro p _
      exact congrArg (fun x : ℝ => w p * x) (sum_indicator_prescribed (a p) (b p))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; exact mul_comm _ _

end OnlineSteinerForest.LowerBound.Probability
