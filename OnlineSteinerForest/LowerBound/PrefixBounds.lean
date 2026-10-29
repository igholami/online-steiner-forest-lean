import OnlineSteinerForest.LowerBound.PowerEstimates
import OnlineSteinerForest.LowerBound.Size

/-! Bounds for the first positive matching rank, including ceiling roundoff. -/
namespace OnlineSteinerForest.LowerBound

theorem prefix_mass_ge_linear (h : ℕ) :
    (256 : ℚ) * h ≤ prefixFraction h * matchingSize h := by
  unfold prefixFraction
  norm_num only [Nat.cast_ofNat, pow_succ, pow_zero, mul_one, mul_assoc]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (Nat.cast_pos.mpr (logSize_pos h))).mpr
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (logSize_le_matchingSize h)) (by positivity)

theorem prefix_mass_ge_two (h : ℕ) (hh : 32 ≤ h) :
    (2 : ℚ) ≤ prefixFraction h * matchingSize h := by
  have hl := prefix_mass_ge_linear h
  have hh' : (32 : ℚ) ≤ h := Nat.cast_le.mpr hh
  linarith

theorem firstRank_pos (h : ℕ) (hh : 32 ≤ h) : 0 < firstRank h := by
  apply Nat.ceil_pos.mpr
  linarith [prefix_mass_ge_two h hh]

theorem firstRank_le_matchingSize (h : ℕ) (hh : 32 ≤ h) : firstRank h ≤ matchingSize h := by
  apply Nat.ceil_le.mpr
  have he := prefixFraction_le_quarter h hh
  calc
    prefixFraction h * matchingSize h ≤ (1 : ℚ) * matchingSize h :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    _ = _ := one_mul _

theorem firstRank_le_twice_mass (h : ℕ) (hh : 32 ≤ h) :
    (firstRank h : ℚ) ≤ 2 * prefixFraction h * matchingSize h := by
  have hm := prefix_mass_ge_two h hh
  have hc := Nat.ceil_lt_add_one (show (0 : ℚ) ≤ prefixFraction h * matchingSize h by linarith)
  change (firstRank h : ℚ) < prefixFraction h * matchingSize h + 1 at hc
  linarith

theorem firstRank_sub_one_ge_half_mass (h : ℕ) (hh : 32 ≤ h) :
    prefixFraction h * matchingSize h / 2 ≤ (firstRank h - 1 : ℕ) := by
  have hm := prefix_mass_ge_two h hh
  have hc := Nat.le_ceil (prefixFraction h * matchingSize h)
  change prefixFraction h * matchingSize h ≤ (firstRank h : ℚ) at hc
  rw [Nat.cast_sub (firstRank_pos h hh), Nat.cast_one]
  linarith

end OnlineSteinerForest.LowerBound
