import OnlineSteinerForest.LowerBound.PatternSeries
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-! Finite positive run-length/direction choices are bounded by the geometric run weight. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

noncomputable def runChoiceWeight {B : ℕ} (ρ : ℝ) (d : Fin B × Bool) : ℝ :=
  Real.exp (-(16 * ρ) * (((d.1.val + 1 : ℕ) : ℝ)))

theorem finite_run_weight_le (B : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∑ d : Fin B × Bool, runChoiceWeight ρ d) ≤ runWeight ρ := by
  let r := Real.exp (-(16 * ρ))
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have ht (d : Fin B × Bool) : runChoiceWeight ρ d = r * r ^ d.1.val := by
    unfold runChoiceWeight
    rw [mul_comm, Real.exp_nat_mul, pow_succ]
    ring
  have hsum : (∑ d : Fin B × Bool, runChoiceWeight ρ d) =
      2 * r * ∑ t ∈ Finset.range B, r ^ t := by
    simp_rw [ht]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul,
      Nat.cast_ofNat]
    rw [Fin.sum_univ_eq_sum_range (fun t => 2 * (r * r ^ t)) B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hs := (hasSum_geometric_of_lt_one hr0 hr1).summable.sum_le_tsum
    (Finset.range B) (fun t _ => pow_nonneg hr0 t)
  rw [tsum_geometric_of_lt_one hr0 hr1] at hs
  have hden : 1 - (Real.exp (16 * ρ))⁻¹ ≠ 0 := by
    rw [← Real.exp_neg]
    exact sub_ne_zero.mpr (ne_of_gt hr1)
  have heq : 2 * r * (1 - r)⁻¹ = runWeight ρ := by
    dsimp [r, runWeight]
    rw [Real.exp_neg]
    field_simp [hden, Real.exp_ne_zero, (show Real.exp (16 * ρ) - 1 ≠ 0 by
      have he := Real.add_one_le_exp (16 * ρ)
      linarith)]
  rw [hsum, ← heq]
  exact mul_le_mul_of_nonneg_left hs (mul_nonneg (by norm_num) hr0)

theorem finite_run_vectors_le (B q : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∑ runs : Fin (q + 1) → (Fin B × Bool),
      ∏ j : Fin (q + 1), runChoiceWeight ρ (runs j)) ≤ runWeight ρ ^ (q + 1) := by
  rw [← Fintype.prod_sum]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun d _ => Real.exp_nonneg _))
    (finite_run_weight_le B ρ hρ) _

end OnlineSteinerForest.LowerBound
