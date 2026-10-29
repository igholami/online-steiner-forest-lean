import OnlineSteinerForest.LowerBound.Tests
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp

/-! Sum of exponentially weighted run patterns in the random-matching estimate. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

noncomputable def runWeight (q : ℝ) : ℝ := 2 / (Real.exp (16 * q) - 1)

theorem runWeight_nonneg (q : ℝ) (hq : 0 < q) : 0 ≤ runWeight q := by
  have he := Real.add_one_le_exp (16 * q)
  unfold runWeight
  apply div_nonneg (by norm_num)
  linarith

theorem runWeight_le (q : ℝ) (hq : 0 < q) : runWeight q ≤ 1 / (8 * q) := by
  have he := Real.add_one_le_exp (16 * q)
  have hden : 0 < Real.exp (16 * q) - 1 := by linarith
  unfold runWeight
  apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hq)).mpr
  nlinarith

theorem runWeight_mul_le_quarter (q μ : ℝ) (hq : 0 < q) (hμ : μ ≤ 2 * q) :
    runWeight q * μ ≤ 1 / 4 := by
  have hR := runWeight_nonneg q hq
  have hbound := (le_div_iff₀ (mul_pos (by norm_num) hq)).mp (runWeight_le q hq)
  have hmul := mul_le_mul_of_nonneg_left hμ hR
  nlinarith

theorem pattern_series_eq (R μ : ℝ) (hR : 0 ≤ R) (hμ : 0 ≤ μ) (hprod : R * μ < 1) :
    (∑' k : ℕ, R ^ (k + 1) * μ ^ k) = R / (1 - R * μ) := by
  have hterm (k : ℕ) : R ^ (k + 1) * μ ^ k = R * (R * μ) ^ k := by
    rw [pow_succ, mul_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (mul_nonneg hR hμ) hprod]
  rfl

theorem pattern_series_le (q μ : ℝ) (hq : 0 < q) (hμ0 : 0 ≤ μ) (hμ : μ ≤ 2 * q) :
    (∑' k : ℕ, runWeight q ^ (k + 1) * μ ^ k) ≤ 1 / (6 * q) := by
  have hR := runWeight_nonneg q hq
  have hprod := runWeight_mul_le_quarter q μ hq hμ
  rw [pattern_series_eq _ _ hR hμ0 (by linarith)]
  have hden : 0 < 1 - runWeight q * μ := by linarith
  apply (div_le_div_iff₀ hden (mul_pos (by norm_num) hq)).mpr
  have hbound := (le_div_iff₀ (mul_pos (by norm_num) hq)).mp (runWeight_le q hq)
  nlinarith

end OnlineSteinerForest.LowerBound
