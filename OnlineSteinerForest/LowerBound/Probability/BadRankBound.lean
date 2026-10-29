import OnlineSteinerForest.LowerBound.Probability.BadRankCover
import OnlineSteinerForest.LowerBound.Probability.PatternBound
import OnlineSteinerForest.LowerBound.Probability.FiniteSeries

/-! The manuscript's bad-rank probability estimate for the actual distance test. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem badRankProbability_le (h : ℕ) (hh : 32 ≤ h) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1) :
    badRankProbability h i ≤ (vertexCount h : ℝ) ^ (1 / 32 : ℝ) /
      (2 * vertexCount h * rankFraction h i) := by
  let ρ := rankFraction h i
  let E := (vertexCount h : ℝ) ^ (1 / 32 : ℝ)
  let K := 2 * E / vertexCount h
  have hρ : 0 < ρ := rankFraction_pos h i
  have hN : (0 : ℝ) < vertexCount h := by
    exact_mod_cast Nat.two_pow_pos (logSize h)
  have hK : 0 ≤ K := by dsimp [K, E]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  calc
    _ ≤ ∑ p : Pattern h i, p.2.val.weight *
        (2 / (2 * (matchingSize h : ℝ)) ^ (2 * p.1.val + 2)) :=
      badRankProbability_le_patterns h hh i hi
    _ = ∑ q : Fin (logSize h ^ 2),
        ∑ p : {p : RawPattern h i q.val // p.Valid}, p.val.weight *
          (2 / (2 * (matchingSize h : ℝ)) ^ (2 * q.val + 2)) := by
      exact Fintype.sum_sigma _
    _ ≤ ∑ q : Fin (logSize h ^ 2),
        (∑ p : RawPattern h i q.val, p.weight) *
          (2 / (2 * (matchingSize h : ℝ)) ^ (2 * q.val + 2)) := by
      apply Finset.sum_le_sum
      intro q _
      rw [Finset.sum_mul]
      exact sum_subtype_le_sum _ _ (fun p => mul_nonneg p.weight_nonneg (by positivity))
    _ ≤ ∑ q : Fin (logSize h ^ 2),
        K * runWeight ρ ^ (q.val + 1) * (2 * ρ) ^ q.val := by
      exact Finset.sum_le_sum (fun q _ => normalized_raw_pattern_sum_le h hh i hi q.val (by omega))
    _ = K * ∑ q : Fin (logSize h ^ 2), runWeight ρ ^ (q.val + 1) * (2 * ρ) ^ q.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ ≤ K * (1 / (6 * ρ)) := mul_le_mul_of_nonneg_left
      (finite_pattern_series_le (logSize h ^ 2) ρ hρ) hK
    _ ≤ _ := by
      have heq : K * (1 / (6 * ρ)) = E / (3 * (vertexCount h : ℝ) * ρ) := by
        dsimp [K]
        (field_simp; ring)
      rw [heq]
      exact div_le_div_of_nonneg_left hE (by positivity)
        (by have := mul_pos hN hρ; nlinarith)

end OnlineSteinerForest.LowerBound.Probability
