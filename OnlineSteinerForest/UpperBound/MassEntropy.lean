import OnlineSteinerForest.Graph.Cost
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Entropy estimate used to sum maximum-cost component lifetimes. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*}

/-- Shannon's elementary cardinality bound, with natural logarithms. -/
theorem entropy_le_log_card (s : Finset ι) (hs : s.Nonempty) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 < p i) (hsum : ∑ i ∈ s, p i = 1) :
    ∑ i ∈ s, p i * Real.log (1 / p i) ≤ Real.log s.card := by
  have hk : (0 : ℝ) < s.card := Nat.cast_pos.mpr hs.card_pos
  have hterm : ∀ i ∈ s, p i * Real.log (1 / p i) ≤
      p i * Real.log s.card + (1 / s.card - p i) := by
    intro i hi
    have hpi := hp i hi
    have hlog := Real.log_le_sub_one_of_pos (div_pos zero_lt_one (mul_pos hk hpi))
    have hmul := mul_le_mul_of_nonneg_left hlog hpi.le
    have hrewrite : p i * Real.log (1 / p i) =
        p i * Real.log s.card + p i * Real.log (1 / ((s.card : ℝ) * p i)) := by
      rw [Real.log_div one_ne_zero hpi.ne', Real.log_div one_ne_zero (mul_ne_zero hk.ne' hpi.ne'),
        Real.log_one, Real.log_mul hk.ne' hpi.ne']
      ring
    have hinv : p i * (1 / ((s.card : ℝ) * p i)) = 1 / s.card := by
      field_simp
    calc
      _ = _ := hrewrite
      _ ≤ p i * Real.log s.card + p i * (1 / ((s.card : ℝ) * p i) - 1) :=
        add_le_add le_rfl hmul
      _ = _ := by rw [mul_sub, hinv, mul_one]
  calc
    _ ≤ ∑ i ∈ s, (p i * Real.log s.card + (1 / s.card - p i)) := Finset.sum_le_sum hterm
    _ = Real.log s.card := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum]
      simp only [one_mul, Finset.sum_const, nsmul_eq_mul]
      field_simp
      ring

/-- Weighted form of the entropy bound, before converting logarithm bases. -/
theorem sum_weight_mul_log_ratio_le (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * Real.log ((∑ j ∈ s, w j) / w i)) ≤
      (∑ i ∈ s, w i) * Real.log s.card := by
  let A := ∑ i ∈ s, w i
  have hA : 0 < A := Finset.sum_pos hw hs
  have hsum : ∑ i ∈ s, w i / A = 1 := by
    rw [← Finset.sum_div]
    exact div_self hA.ne'
  have he := entropy_le_log_card s hs (fun i => w i / A)
    (fun i hi => div_pos (hw i hi) hA) hsum
  have hmul := mul_le_mul_of_nonneg_left he hA.le
  rw [Finset.mul_sum] at hmul
  apply hmul.trans_eq'
  apply Finset.sum_congr rfl
  intro i hi
  rw [one_div_div]
  have hcancel : A * (w i / A) = w i := by field_simp
  rw [← mul_assoc, hcancel]

end OnlineSteinerForest.UpperBound
