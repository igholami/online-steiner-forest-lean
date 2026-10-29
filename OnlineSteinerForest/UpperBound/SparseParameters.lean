import OnlineSteinerForest.UpperBound.CycleNumericalCap

/-! Exact zone size, parallel-edge cap, and peeling threshold from the manuscript. -/
namespace OnlineSteinerForest.UpperBound

def zoneMultiplier (L : ℕ) : ℕ := 65536 * L ^ 3
noncomputable def parallelCap (L : ℕ) : ℕ :=
  ⌈4096 * (zoneMultiplier L : ℝ) * Real.logb 2 (512 * zoneMultiplier L)⌉₊
noncomputable def coreDegree (L : ℕ) : ℕ := 8191 * parallelCap L

theorem zoneMultiplier_ge (L : ℕ) (hL : 1 ≤ L) : (65536 : ℝ) ≤ zoneMultiplier L := by
  have hp : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ (Nat.one_le_cast.mpr hL)
  unfold zoneMultiplier
  push_cast
  nlinarith

theorem parallelCap_pos (L : ℕ) (hL : 1 ≤ L) : 0 < parallelCap L := by
  have hM := zoneMultiplier_ge L hL
  have hZ := seventeen_le_zoneLog (zoneMultiplier L : ℝ) (by linarith)
  apply Nat.ceil_pos.mpr
  positivity

theorem multiplicity_le_parallelCap (L q : ℕ) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (h : (q : ℝ) - 1 ≤ 48 * (zoneMultiplier L : ℝ) * cycleFactor q) : q ≤ parallelCap L := by
  exact multiplicity_cap (zoneMultiplier L) (by have hh := zoneMultiplier_ge L hL; linarith) q hq h

end OnlineSteinerForest.UpperBound
