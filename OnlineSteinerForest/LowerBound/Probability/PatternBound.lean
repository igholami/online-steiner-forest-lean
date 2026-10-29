import OnlineSteinerForest.LowerBound.Probability.PatternSum
import OnlineSteinerForest.LowerBound.Probability.ShortcutMoment
import OnlineSteinerForest.LowerBound.RunWeights
import OnlineSteinerForest.LowerBound.ExponentialPrefactor
import OnlineSteinerForest.LowerBound.PatternSize

/-! Bound each fixed-shortcut-count pattern sum after its permutation normalization. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem pattern_rank_count_le (h : ℕ) (hh : 32 ≤ h) (q : ℕ) (hq : q + 1 ≤ logSize h ^ 2) :
    q + 1 ≤ matchingSize h := by
  have hs := pattern_constraint_sq_le h hh q hq
  have hk : 2 * q + 2 ≤ (2 * q + 2) ^ 2 := by nlinarith
  rw [← twice_matchingSize h] at hs
  omega

theorem pattern_exp_prefactor_le (h : ℕ) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) :
    Real.exp (16 * rankFraction h i * rankPrice h i) ≤ (vertexCount h : ℝ) ^ (1 / 32 : ℝ) := by
  simpa only [rankFraction, mul_div_assoc] using exp_tilt_price_le h i hi

theorem sum_raw_pattern_weights_le (h : ℕ) (hh : 32 ≤ h) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) (q : ℕ) (hq : q + 1 ≤ logSize h ^ 2) :
    (∑ p : RawPattern h i q, p.weight) ≤
      (2 * (matchingSize h : ℝ)) ^ (q + 1) * (2 : ℝ) ^ q *
        (vertexCount h : ℝ) ^ (1 / 32 : ℝ) * runWeight (rankFraction h i) ^ (q + 1) *
        ((matchingSize h : ℝ) ^ q * (2 * rankFraction h i) ^ q) := by
  let ρ := rankFraction h i
  have hρ : 0 < ρ := rankFraction_pos h i
  have hR : 0 ≤ runWeight ρ := runWeight_nonneg ρ hρ
  have hE := pattern_exp_prefactor_le h i hi
  have hrun := finite_run_vectors_le (logSize h ^ 2) q ρ hρ
  have hrank := shortcut_assignment_sum_le h hh i hi q (pattern_rank_count_le h hh q hq)
  have hAnn : (0 : ℝ) ≤ ∑ runs : Fin (q + 1) → (Fin (logSize h ^ 2) × Bool),
      ∏ j : Fin (q + 1), runChoiceWeight ρ (runs j) := by
    exact Finset.sum_nonneg (fun runs _ => Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le))
  have hprefix : (0 : ℝ) ≤ (2 * (matchingSize h : ℝ)) ^ (q + 1) * (2 : ℝ) ^ q := by positivity
  rw [sum_raw_pattern_weights]
  change _ ≤ _
  calc
    _ ≤ (2 * (matchingSize h : ℝ)) ^ (q + 1) * (2 : ℝ) ^ q *
        Real.exp (16 * ρ * rankPrice h i) *
        (∑ runs : Fin (q + 1) → (Fin (logSize h ^ 2) × Bool),
          ∏ j : Fin (q + 1), runChoiceWeight ρ (runs j)) *
        ((matchingSize h : ℝ) ^ q * (2 * ρ) ^ q) :=
      mul_le_mul_of_nonneg_left hrank (mul_nonneg (mul_nonneg hprefix (Real.exp_pos _).le) hAnn)
    _ ≤ (2 * (matchingSize h : ℝ)) ^ (q + 1) * (2 : ℝ) ^ q *
        Real.exp (16 * ρ * rankPrice h i) * runWeight ρ ^ (q + 1) *
        ((matchingSize h : ℝ) ^ q * (2 * ρ) ^ q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hrun (mul_nonneg hprefix (Real.exp_pos _).le)) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hprefix) (by positivity)) (by positivity)

private theorem normalization_identity (N m E R μ : ℝ) (q : ℕ) (hN : N ≠ 0) (hm : N = 2 * m) :
    (N ^ (q + 1) * (2 : ℝ) ^ q * E * R ^ (q + 1) * (m ^ q * μ ^ q)) *
      (2 / N ^ (2 * q + 2)) = (2 * E / N) * R ^ (q + 1) * μ ^ q := by
  have ht : (2 : ℝ) ^ q * m ^ q = N ^ q := by rw [← mul_pow, ← hm]
  have hn : N ^ (2 * q + 2) = (N ^ (q + 1) * N ^ q) * N := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hnum : N ^ (q + 1) * (2 : ℝ) ^ q * E * R ^ (q + 1) * (m ^ q * μ ^ q) =
      N ^ (q + 1) * N ^ q * E * R ^ (q + 1) * μ ^ q := by rw [← ht]; ring
  rw [hnum, hn]
  field_simp

theorem normalized_raw_pattern_sum_le (h : ℕ) (hh : 32 ≤ h) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) (q : ℕ) (hq : q + 1 ≤ logSize h ^ 2) :
    (∑ p : RawPattern h i q, p.weight) * (2 / (2 * (matchingSize h : ℝ)) ^ (2 * q + 2)) ≤
      (2 * (vertexCount h : ℝ) ^ (1 / 32 : ℝ) / vertexCount h) *
        runWeight (rankFraction h i) ^ (q + 1) * (2 * rankFraction h i) ^ q := by
  have hm : (0 : ℝ) < matchingSize h := Nat.cast_pos.mpr (Nat.zero_lt_of_lt i.isLt)
  calc
    _ ≤ _ * (2 / (2 * (matchingSize h : ℝ)) ^ (2 * q + 2)) :=
      mul_le_mul_of_nonneg_right (sum_raw_pattern_weights_le h hh i hi q hq) (by positivity)
    _ = _ := by
      rw [normalization_identity _ _ _ _ _ q (by positivity) rfl]
      rw [← twice_matchingSize h, Nat.cast_mul, Nat.cast_ofNat]

end OnlineSteinerForest.LowerBound.Probability
