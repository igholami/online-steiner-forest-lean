import OnlineSteinerForest.UpperBound.CycleNumericalCap

/-! The small-tree count has cycle factor at most `36 H(L)`, as in the manuscript. -/
namespace OnlineSteinerForest.UpperBound

theorem cycleFactor_ge_logb_add_four (L : ℕ) (hL : 1 ≤ L) :
    Real.logb 2 (L : ℝ) + 4 ≤ cycleFactor L := by
  have hLp : 0 < (L : ℝ) := Nat.cast_pos.mpr (by omega)
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    simpa only [show (2 : ℝ) ^ 3 = 8 by norm_num, Nat.cast_ofNat] using logb_two_pow 3
  have heq : Real.logb 2 (8 * (L : ℝ)) = 3 + Real.logb 2 L := by
    rw [logb_two_mul _ _ (by norm_num) hLp, h8]
  have hc := Nat.le_ceil (Real.logb 2 (8 * (L : ℝ)))
  have hd : (cycleFactor L : ℝ) = (⌈Real.logb 2 (8 * (L : ℝ))⌉₊ : ℝ) + 1 := by
    simp only [cycleFactor, Nat.cast_add, Nat.cast_one]
  linarith

theorem small_count_cycleFactor_le (L q : ℕ) (hL : 4 ≤ L) (hq : 1 ≤ q)
    (hfixed : (q : ℝ) - 1 ≤ 48 * (65536 * (L : ℝ) ^ 3) * cycleFactor q) :
    (cycleFactor q : ℝ) ≤ 36 * cycleFactor L := by
  let M : ℝ := 65536 * (L : ℝ) ^ 3
  have hL4 : (4 : ℝ) ≤ L := Nat.cast_le.mpr hL
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hLp : 0 < (L : ℝ) := by linarith
  have hM : 256 ≤ M := by
    have hp : (1 : ℝ) ≤ (L : ℝ) ^ 3 := one_le_pow₀ hL1
    dsimp [M]
    nlinarith
  have hlogM : Real.logb 2 (512 * M) = 25 + 3 * Real.logb 2 (L : ℝ) := by
    rw [show 512 * M = (2 : ℝ) ^ 25 * (L : ℝ) ^ 3 by dsimp [M]; ring]
    rw [logb_two_mul _ _ (by positivity) (by positivity), logb_two_pow, Real.logb_pow]
    norm_num
  have h13 : 25 + 3 * Real.logb 2 (L : ℝ) ≤ 13 * L := by
    nlinarith [logb_two_le_two_mul (L : ℝ) hLp]
  have hcap := multiplicity_real_cap M hM q hq hfixed
  rw [hlogM] at hcap
  have hpoly : (q : ℝ) ≤ (2 : ℝ) ^ 32 * (L : ℝ) ^ 4 := by
    have hm := mul_le_mul_of_nonneg_left h13 (show 0 ≤ 4096 * M by dsimp [M]; positivity)
    have hh := hcap.trans hm
    dsimp [M] at hh
    nlinarith [pow_nonneg hLp.le 4]
  have hlogq := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
    (Nat.cast_pos.mpr (show 0 < q by omega)) hpoly
  rw [logb_two_mul _ _ (by positivity) (by positivity), logb_two_pow, Real.logb_pow] at hlogq
  have hHq := cycleFactor_le_log q hq
  change (cycleFactor q : ℝ) ≤ Real.logb 2 (q : ℝ) + 5 at hHq
  have hHL := cycleFactor_ge_logb_add_four L (by omega)
  have hx : 0 ≤ Real.logb 2 (L : ℝ) :=
    div_nonneg (Real.log_nonneg hL1) log_two_pos.le
  norm_num at hlogq
  nlinarith

end OnlineSteinerForest.UpperBound
