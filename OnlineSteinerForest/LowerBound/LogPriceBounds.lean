import OnlineSteinerForest.LowerBound.PrefixBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

/-! Logarithmic size of the retained harmonic tail. -/
namespace OnlineSteinerForest.LowerBound

theorem log_tail_ratio_lower (h : ℕ) (hh : 32 ≤ h) :
    (h : ℝ) * Real.log 2 / 2 ≤ Real.log ((logSize h : ℝ) / (512 * h)) := by
  have hhpos : 0 < h := by omega
  have hxpos : (0 : ℝ) < 512 * h := mul_pos (by norm_num) (Nat.cast_pos.mpr hhpos)
  have hpow : (512 : ℝ) * h ≤ (2 : ℝ) ^ (h / 2) := by
    exact_mod_cast scaled_linear_le_half_power h hh
  have hlog := Real.log_le_log hxpos hpow
  rw [Real.log_pow] at hlog
  have hhalf : (h / 2 : ℕ) * 2 ≤ h := Nat.div_mul_le_self h 2
  have hhalf' : ((h / 2 : ℕ) : ℝ) * 2 ≤ h := by exact_mod_cast hhalf
  have hln : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hprod := mul_le_mul_of_nonneg_right hhalf' hln.le
  rw [Real.log_div (Nat.cast_ne_zero.mpr (logSize_pos h).ne') hxpos.ne']
  simp only [logSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  linarith

theorem tail_ratio_le (h : ℕ) (hh : 32 ≤ h) :
    (logSize h : ℚ) / (512 * h) ≤ ((matchingSize h + 1 : ℕ) : ℚ) / firstRank h := by
  have hL : (0 : ℚ) < logSize h := Nat.cast_pos.mpr (logSize_pos h)
  have ha : (0 : ℚ) < firstRank h := Nat.cast_pos.mpr (firstRank_pos h hh)
  have hhpos : 0 < h := by omega
  have hden : (0 : ℚ) < 512 * h := mul_pos (by norm_num) (Nat.cast_pos.mpr hhpos)
  have hb := firstRank_le_twice_mass h hh
  have heq : 2 * prefixFraction h * matchingSize h =
      (512 : ℚ) * h * matchingSize h / logSize h := by
    unfold prefixFraction
    norm_num
    ring
  rw [heq] at hb
  have hb' := (le_div_iff₀ hL).mp hb
  apply (div_le_div_iff₀ hden ha).mpr
  push_cast
  nlinarith

theorem log_harmonic_tail_lower (h : ℕ) (hh : 32 ≤ h) :
    (h : ℝ) * Real.log 2 / 2 ≤
      Real.log (((matchingSize h + 1 : ℕ) : ℝ) / firstRank h) := by
  have hratio : (logSize h : ℝ) / (512 * h) ≤
      ((matchingSize h + 1 : ℕ) : ℝ) / firstRank h := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (tail_ratio_le h hh)
    simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hc
  have hpos : (0 : ℝ) < (logSize h : ℝ) / (512 * h) := by
    have : 0 < h := by omega
    exact div_pos (Nat.cast_pos.mpr (logSize_pos h)) (by positivity)
  exact (log_tail_ratio_lower h hh).trans (Real.log_le_log hpos hratio)

end OnlineSteinerForest.LowerBound
