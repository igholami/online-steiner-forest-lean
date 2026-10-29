import OnlineSteinerForest.UpperBound.CycleLogarithms

/-! The numerical multiplicity cap (Lemma `lem:numerical` in the manuscript). -/
namespace OnlineSteinerForest.UpperBound

/-- The logarithmic fixed-point inequality implies an explicit finite cap.
The proof uses the concavity bound for log and avoids differentiating a ceiling. -/
theorem multiplicity_real_cap (M : ℝ) (hM : 256 ≤ M) (q : ℕ) (hq : 1 ≤ q)
    (h : (q : ℝ) - 1 ≤ 48 * M * cycleFactor q) :
    (q : ℝ) ≤ 4096 * M * Real.logb 2 (512 * M) := by
  let Z := Real.logb 2 (512 * M)
  let K := 4096 * M * Z
  have hZ : 17 ≤ Z := seventeen_le_zoneLog M hM
  have hMpos : 0 < M := by linarith
  have hZpos : 0 < Z := by linarith
  have hKpos : 0 < K := by dsimp [K]; positivity
  have hqpos : (0 : ℝ) < q := Nat.cast_pos.mpr (by omega)
  have hlogK : Real.logb 2 K + 5 ≤ 4 * Z := by
    have heq : K = 8 * (512 * M) * Z := by dsimp [K]; ring
    rw [heq, logb_two_mul _ _ (by positivity) hZpos,
      logb_two_mul _ _ (by norm_num) (by positivity)]
    have h8 : Real.logb 2 (8 : ℝ) = 3 := by
      simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using logb_two_pow 3
    rw [h8]
    change 3 + Z + Real.logb 2 Z + 5 ≤ 4 * Z
    linarith [logb_two_le_two_mul Z hZpos]
  have hlogq : Real.logb 2 (q : ℝ) = Real.logb 2 K + Real.logb 2 ((q : ℝ) / K) := by
    simp only [Real.logb, Real.log_div hqpos.ne' hKpos.ne']
    ring
  have hHq : (cycleFactor q : ℝ) ≤ 4 * Z + 2 * ((q : ℝ) / K) := by
    have hc := cycleFactor_le_log q hq
    change (cycleFactor q : ℝ) ≤ Real.logb 2 (q : ℝ) + 5 at hc
    rw [hlogq] at hc
    linarith [logb_two_le_two_mul ((q : ℝ) / K) (div_pos hqpos hKpos)]
  have hcoeff : 96 * M / K ≤ 1 / 32 := by
    apply (div_le_iff₀ hKpos).mpr
    dsimp [K]
    nlinarith [mul_nonneg hMpos.le (show 0 ≤ Z - 1 by linarith)]
  have hterm : 96 * M * ((q : ℝ) / K) ≤ (q : ℝ) / 32 := by
    have hh := mul_le_mul_of_nonneg_right hcoeff hqpos.le
    convert hh using 1 <;> ring
  have hlinear : (q : ℝ) - 1 ≤ 192 * M * Z + (q : ℝ) / 32 := by
    have hh := h.trans (mul_le_mul_of_nonneg_left hHq (by positivity))
    nlinarith
  have hMZ : 1 ≤ M * Z := by
    nlinarith [mul_nonneg (show 0 ≤ M - 1 by linarith) (show 0 ≤ Z - 1 by linarith)]
  change (q : ℝ) ≤ K
  dsimp [K]
  nlinarith

/-- Integral version used for loops and parallel edges in the zone graph. -/
theorem multiplicity_cap (M : ℝ) (hM : 256 ≤ M) (q : ℕ) (hq : 1 ≤ q)
    (h : (q : ℝ) - 1 ≤ 48 * M * cycleFactor q) :
    q ≤ ⌈4096 * M * Real.logb 2 (512 * M)⌉₊ := by
  have hreal := (multiplicity_real_cap M hM q hq h).trans (Nat.le_ceil _)
  exact_mod_cast hreal

end OnlineSteinerForest.UpperBound
