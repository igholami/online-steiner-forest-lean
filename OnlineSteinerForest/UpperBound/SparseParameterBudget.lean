import OnlineSteinerForest.UpperBound.SparseParameterLogarithms

/-! The exact manuscript constant for the discarded auxiliary-edge budget. -/
namespace OnlineSteinerForest.UpperBound

theorem parallelCap_add_coreDegree_le (L : ℕ) (hL : 1 ≤ L) :
    ((parallelCap L + coreDegree L : ℕ) : ℝ) ≤
      (2 : ℝ) ^ 28 * cycleFactor L * zoneMultiplier L := by
  have hM := zoneMultiplier_ge L hL
  have hZ0 := seventeen_le_zoneLog (zoneMultiplier L : ℝ) (by linarith)
  have hZ := zoneLog_le_seven_cycleFactor L hL
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 4096 * (zoneMultiplier L : ℝ) *
    Real.logb 2 (512 * zoneMultiplier L) by positivity)).le
  have hbound : (parallelCap L : ℝ) ≤ 4096 * (zoneMultiplier L : ℝ) *
      (7 * cycleFactor L) + 1 := by
    have hh := mul_le_mul_of_nonneg_left hZ (show 0 ≤ 4096 * (zoneMultiplier L : ℝ) by positivity)
    exact hceil.trans (add_le_add hh le_rfl)
  have hH : (1 : ℝ) ≤ cycleFactor L := by exact_mod_cast cycleFactor_pos L
  have hMH : (1 : ℝ) ≤ (zoneMultiplier L : ℝ) * cycleFactor L :=
    one_le_mul_of_one_le_of_one_le (by linarith) hH
  unfold coreDegree
  push_cast
  norm_num
  nlinarith

/-- Convert the purely combinatorial peeling bound using the lower cost of each zone. -/
theorem discarded_count_scale_le (L zones discarded : ℕ) (hL : 1 ≤ L) (scale C : ℝ)
    (hscale : 0 ≤ scale)
    (hcount : discarded ≤ (parallelCap L + coreDegree L) * zones)
    (hzones : (zones : ℝ) * zoneMultiplier L * scale ≤ C) :
    (discarded : ℝ) * scale ≤ (2 : ℝ) ^ 28 * cycleFactor L * C := by
  have hparam := parallelCap_add_coreDegree_le L hL
  have hcount' : (discarded : ℝ) ≤ (parallelCap L + coreDegree L : ℕ) * (zones : ℝ) := by exact_mod_cast hcount
  calc
    _ ≤ (((parallelCap L + coreDegree L : ℕ) : ℝ) * (zones : ℝ)) * scale :=
      mul_le_mul_of_nonneg_right hcount' hscale
    _ ≤ ((2 : ℝ) ^ 28 * cycleFactor L * zoneMultiplier L * (zones : ℝ)) * scale := by gcongr
    _ = ((2 : ℝ) ^ 28 * cycleFactor L) * ((zones : ℝ) * zoneMultiplier L * scale) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hzones (by positivity)

end OnlineSteinerForest.UpperBound
