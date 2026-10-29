import OnlineSteinerForest.UpperBound.SparseParameters

/-! The parallel cap grows only logarithmically in the large-tree parameter. -/
namespace OnlineSteinerForest.UpperBound

theorem logb_zoneMultiplier (L : ℕ) (hL : 1 ≤ L) :
    Real.logb 2 (512 * (zoneMultiplier L : ℝ)) = 25 + 3 * Real.logb 2 L := by
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have heq : 512 * (zoneMultiplier L : ℝ) = (2 : ℝ) ^ 25 * (L : ℝ) ^ 3 := by
    simp only [zoneMultiplier, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    norm_num
    ring
  rw [heq, logb_two_mul _ _ (by positivity) (by positivity), logb_two_pow, Real.logb_pow]
  norm_num

theorem logb_add_four_le_cycleFactor (L : ℕ) (hL : 1 ≤ L) :
    Real.logb 2 L + 4 ≤ (cycleFactor L : ℝ) := by
  have hh := Nat.le_ceil (Real.logb 2 (8 * (L : ℝ)))
  have hlog : Real.logb 2 (8 * (L : ℝ)) = 3 + Real.logb 2 L := by
    rw [logb_two_mul _ _ (by norm_num) (by exact_mod_cast (show 0 < L by omega))]
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, logb_two_pow]
    norm_num
  rw [hlog] at hh
  unfold cycleFactor
  push_cast
  rw [hlog]
  linarith

theorem zoneLog_le_seven_cycleFactor (L : ℕ) (hL : 1 ≤ L) :
    Real.logb 2 (512 * (zoneMultiplier L : ℝ)) ≤ 7 * cycleFactor L := by
  have ht : 0 ≤ Real.logb 2 (L : ℝ) :=
    div_nonneg (Real.log_nonneg (Nat.one_le_cast.mpr hL)) log_two_pos.le
  have hh := logb_add_four_le_cycleFactor L hL
  rw [logb_zoneMultiplier L hL]
  linarith

end OnlineSteinerForest.UpperBound
