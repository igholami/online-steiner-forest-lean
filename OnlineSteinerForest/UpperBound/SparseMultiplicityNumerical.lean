import OnlineSteinerForest.UpperBound.SparseParameters
import OnlineSteinerForest.UpperBound.GirthComponentAverage

/-! Charging-cycle rank and two zone budgets imply the explicit parallel and loop caps. -/
namespace OnlineSteinerForest.UpperBound

theorem parallel_multiplicity_cap (L q : ℕ) (hL : 1 ≤ L) (hq : 2 ≤ q)
    (scale C : ℝ) (hscale : 0 < scale) (hC : 0 ≤ C)
    (hcost : C ≤ 6 * zoneMultiplier L * scale)
    (hcharge : ((q - 1 : ℕ) : ℝ) * (scale / 2) ≤ 4 * cycleFactor (q - 1) * C) :
    q ≤ parallelCap L := by
  have hH := Girth.cycleFactor_mono (show 1 ≤ q - 1 by omega) (Nat.sub_le q 1)
  have hH' : (cycleFactor (q - 1) : ℝ) ≤ cycleFactor q := Nat.cast_le.mpr hH
  have hc1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH' (by norm_num : (0 : ℝ) ≤ 4)) hC
  have hc2 := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 4 * (cycleFactor q : ℝ) by positivity)
  rw [Nat.cast_sub (by omega), Nat.cast_one] at hcharge
  have hh : ((q : ℝ) - 1) * scale ≤ (48 * (zoneMultiplier L : ℝ) * cycleFactor q) * scale := by
    nlinarith [hcharge.trans hc1]
  exact multiplicity_le_parallelCap L q hL (by omega) ((mul_le_mul_iff_left₀ hscale).mp (by simpa [mul_comm] using hh))

theorem loop_multiplicity_cap (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (scale C : ℝ) (hscale : 0 < scale)
    (hcost : C ≤ 3 * zoneMultiplier L * scale)
    (hcharge : (q : ℝ) * (scale / 2) ≤ 4 * cycleFactor q * C) : q ≤ parallelCap L := by
  have hc := mul_le_mul_of_nonneg_left hcost (show 0 ≤ 4 * (cycleFactor q : ℝ) by positivity)
  have hh : (q : ℝ) * scale ≤ (24 * (zoneMultiplier L : ℝ) * cycleFactor q) * scale := by nlinarith
  have hqbound : (q : ℝ) ≤ 24 * (zoneMultiplier L : ℝ) * cycleFactor q :=
    (mul_le_mul_iff_left₀ hscale).mp (by simpa [mul_comm] using hh)
  apply multiplicity_le_parallelCap L q hL hq
  have hn : 0 ≤ (zoneMultiplier L : ℝ) * cycleFactor q := by positivity
  nlinarith

end OnlineSteinerForest.UpperBound
