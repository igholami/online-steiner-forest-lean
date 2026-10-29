import OnlineSteinerForest.LowerBound.MeanBadPrice
import OnlineSteinerForest.LowerBound.PositiveRankSums
import OnlineSteinerForest.LowerBound.Probability.RankWeights
import OnlineSteinerForest.LowerBound.TestComparison

/-! Summing the per-rank bad-probability bound with the actual auxiliary prices. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

open Probability

theorem meanBadPrice_bound_of_rank_bounds (h : ℕ) (hh : 32 ≤ h)
    (hprob : ∀ i : Fin (matchingSize h), firstRank h ≤ i.val + 1 →
      badRankProbability h i ≤ (vertexCount h : ℝ) ^ (1 / 32 : ℝ) /
        (2 * vertexCount h * rankFraction h i)) :
    meanBadPrice h ≤ (logSize h : ℝ) * (vertexCount h : ℝ) ^ (1 / 32 : ℝ) /
      (2048 * (prefixFraction h : ℝ)) := by
  classical
  let C := (logSize h : ℝ) * (vertexCount h : ℝ) ^ (1 / 32 : ℝ) *
    (matchingSize h : ℝ) ^ 2 / (2048 * vertexCount h)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : (0 : ℝ) < matchingSize h := Nat.cast_pos.mpr
    ((logSize_pos h).trans_le (logSize_le_matchingSize h))
  have hN : (0 : ℝ) < vertexCount h := Nat.cast_pos.mpr (vertexCount_pos h)
  have hhpos : 0 < h := by omega
  have hε : (0 : ℝ) < (prefixFraction h : ℝ) := Rat.cast_pos.mpr (prefixFraction_pos h hhpos)
  have hterm (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
      rankPrice h i * ((vertexCount h : ℝ) ^ (1 / 32 : ℝ) /
        (2 * vertexCount h * rankFraction h i)) = C * (((i.val + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
    unfold rankPrice rankFraction
    rw [cast_price_of_ge h _ hi]
    dsimp [C]
    have hi0 : (((i.val + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hm.ne', hN.ne', hi0] <;> ring
  have hA : (prefixFraction h : ℝ) * matchingSize h / 2 ≤ ((firstRank h - 1 : ℕ) : ℝ) := by
    have ht := (Rat.cast_le (K := ℝ)).mpr (firstRank_sub_one_ge_half_mass h hh)
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using ht
  have hinv : (((firstRank h - 1 : ℕ) : ℝ)⁻¹) ≤
      2 / ((prefixFraction h : ℝ) * matchingSize h) := by
    calc
      _ = 1 / ((firstRank h - 1 : ℕ) : ℝ) := by simp only [one_div]
      _ ≤ 1 / ((prefixFraction h : ℝ) * matchingSize h / 2) :=
        one_div_le_one_div_of_le (div_pos (mul_pos hε hm) (by norm_num)) hA
      _ = _ := by field_simp [hε.ne', hm.ne'] <;> ring
  rw [meanBadPrice_eq_sum]
  calc
    _ ≤ ∑ i ∈ positiveRanks h, C * (((i.val + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      have hip : firstRank h ≤ i.val + 1 := (Finset.mem_filter.mp hi).2
      exact (mul_le_mul_of_nonneg_left (hprob i hip) (rankPrice_nonneg h i)).trans_eq (hterm i hip)
    _ = C * ∑ i ∈ positiveRanks h, (((i.val + 1 : ℕ) : ℝ)⁻¹) ^ 2 := (Finset.mul_sum _ _ _).symm
    _ = C * ∑ j ∈ Finset.Icc (firstRank h) (matchingSize h), ((j : ℝ)⁻¹) ^ 2 := by
      rw [sum_positiveRanks_eq_Icc h (firstRank_pos h hh) (fun j : ℕ => ((j : ℝ)⁻¹) ^ 2)]
    _ ≤ C * (((firstRank h - 1 : ℕ) : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (sum_inverse_square_Icc_le _ _ (firstRank_ge_two h hh)) hC
    _ ≤ C * (2 / ((prefixFraction h : ℝ) * matchingSize h)) := mul_le_mul_of_nonneg_left hinv hC
    _ = _ := by
      dsimp [C]
      rw [← twice_matchingSize h, Nat.cast_mul, Nat.cast_ofNat]
      field_simp [hm.ne', hε.ne'] <;> ring

end OnlineSteinerForest.LowerBound
