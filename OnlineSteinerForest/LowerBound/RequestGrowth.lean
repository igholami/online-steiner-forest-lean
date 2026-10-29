import OnlineSteinerForest.LowerBound.GreedyCost
import OnlineSteinerForest.LowerBound.PriceLowerBound
import OnlineSteinerForest.LowerBound.PatternSize
import OnlineSteinerForest.LowerBound.RankBounds
import OnlineSteinerForest.LowerBound.ExponentialPrefactor

/-! Retaining half the price forces arbitrarily many requests in the constructed family. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem vertexCount_ge_scaled_logSize (h : ℕ) (hh : 32 ≤ h) :
    16384 * logSize h ≤ vertexCount h := by
  have hp : 1024 ≤ logSize h ^ 3 := by
    have ht := Nat.pow_le_pow_left (logSize_ge_sixtyfour h hh) 3
    norm_num at ht
    omega
  calc
    _ = 16 * 1024 * logSize h := by ring
    _ ≤ 16 * logSize h ^ 3 * logSize h :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hp)
    _ = 16 * logSize h ^ 4 := by ring
    _ ≤ _ := vertexCount_ge_sixteen_fourth h hh

theorem totalPrice_half_ge_level_sq (h : ℕ) (hh : 32 ≤ h) :
    (h : ℝ) * (logSize h : ℝ) ^ 2 ≤ totalPrice h / 2 := by
  have hNL : (16384 : ℝ) * logSize h ≤ vertexCount h := by
    exact_mod_cast vertexCount_ge_scaled_logSize h hh
  have hlog := mul_le_mul_of_nonneg_left half_lt_log_two.le
    (show (0 : ℝ) ≤ vertexCount h from Nat.cast_nonneg _)
  have hLN : (8192 : ℝ) * logSize h ≤ (vertexCount h : ℝ) * Real.log 2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right hLN
    (mul_nonneg (show (0 : ℝ) ≤ logSize h from Nat.cast_nonneg _)
      (show (0 : ℝ) ≤ h from Nat.cast_nonneg _))
  calc
    _ ≤ (vertexCount h : ℝ) * logSize h * h * Real.log 2 / 8192 := by nlinarith
    _ ≤ _ := by
      have ht := totalPrice_lower h hh
      norm_num at ht ⊢
      linarith

theorem instance_request_count_ge_level (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    h ≤ (instanceRequests h σ).length := by
  classical
  have hlow := (totalPrice_half_ge_level_sq h hh).trans hσ
  have hu : (∑ i ∈ retainedRanks h σ, rankPrice h i) ≤
      ((retainedRanks h σ).card : ℝ) * (logSize h : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _i ∈ retainedRanks h σ, (logSize h : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact rankPrice_le_logSize_sq h hh i (Finset.mem_filter.mp hi).2.1
      _ = _ := by simp [nsmul_eq_mul]
  have hprod := hlow.trans hu
  have hk : (h : ℝ) ≤ (retainedRanks h σ).card :=
    (mul_le_mul_iff_of_pos_right (sq_pos_of_pos (Nat.cast_pos.mpr (logSize_pos h)))).mp hprod
  have hkNat : h ≤ (retainedRanks h σ).card := by exact_mod_cast hk
  simpa only [instanceRequests, requestedPairs_length] using hkNat

end OnlineSteinerForest.LowerBound
