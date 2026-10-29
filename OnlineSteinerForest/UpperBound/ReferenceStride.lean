import OnlineSteinerForest.UpperBound.FinalParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The computed stride absorbs the exact mark-reconnection coefficient. -/
namespace OnlineSteinerForest.UpperBound

theorem batchClass_stride_ge (k : ℕ) :
    (2 : ℝ) ^ 28 * (cycleFactor k : ℝ) ^ 5 ≤ (2 : ℝ) ^ batchClassCount k := by
  have hL : 0 < (cycleFactor k : ℝ) := Nat.cast_pos.mpr (cycleFactor_pos k)
  have hc : 5 * Real.logb 2 (cycleFactor k) ≤
      (⌈5 * Real.logb 2 (cycleFactor k)⌉₊ : ℝ) := Nat.le_ceil _
  have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc
  have heq : (2 : ℝ) ^ (5 * Real.logb 2 (cycleFactor k)) = (cycleFactor k : ℝ) ^ 5 := by
    rw [mul_comm (5 : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hL]
    norm_cast
  rw [heq, Real.rpow_natCast] at hp
  unfold batchClassCount
  rw [pow_add]
  exact mul_le_mul_of_nonneg_left hp (by positivity)

theorem mark_overhead_le_reference (k : ℕ) (marks scale reference : ℝ)
    (hmarks : marks * scale ≤ 8 * cycleFactor k / (2 : ℝ) ^ batchClassCount k * reference)
    (href : 0 ≤ reference) :
    2 ^ 25 * (cycleFactor k : ℝ) ^ 4 * marks * scale ≤ reference := by
  have hstride := batchClass_stride_ge k
  have hpow : 0 < (2 : ℝ) ^ batchClassCount k := pow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hmarks
    (by positivity : (0 : ℝ) ≤ 2 ^ 25 * (cycleFactor k : ℝ) ^ 4)
  have hratio : 2 ^ 25 * (cycleFactor k : ℝ) ^ 4 *
      (8 * cycleFactor k / (2 : ℝ) ^ batchClassCount k) ≤ 1 := by
    rw [show 2 ^ 25 * (cycleFactor k : ℝ) ^ 4 *
      (8 * cycleFactor k / (2 : ℝ) ^ batchClassCount k) =
      ((2 : ℝ) ^ 28 * (cycleFactor k : ℝ) ^ 5) /
        (2 : ℝ) ^ batchClassCount k by ring]
    exact (div_le_iff₀ hpow).mpr (by simpa only [one_mul] using hstride)
  nlinarith [mul_le_mul_of_nonneg_right hratio href]

end OnlineSteinerForest.UpperBound
