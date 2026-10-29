import OnlineSteinerForest.UpperBound.SmallNumerical

/-! The manuscript's `288 H(L)` payment budget for one actual small reference tree. -/
namespace OnlineSteinerForest.UpperBound

theorem small_tree_payment_budget (L q : ℕ) (hL : 4 ≤ L)
    (scale treeCost paid : ℝ) (hscale : 0 < scale) (hcost : 0 ≤ treeCost)
    (hsmall : treeCost < 65536 * (L : ℝ) ^ 3 * scale)
    (hthreshold : (q : ℝ) * scale ≤ 4 * cycleFactor q * treeCost)
    (hpaid : paid ≤ 2 * q * scale) :
    paid ≤ 288 * cycleFactor L * treeCost := by
  by_cases hq : q = 0
  · simp only [hq, Nat.cast_zero, mul_zero, zero_mul] at hpaid
    exact hpaid.trans (by positivity)
  · have hqpos : 1 ≤ q := by omega
    have hM : 0 ≤ 65536 * (L : ℝ) ^ 3 := by positivity
    have hH : 0 ≤ (cycleFactor q : ℝ) := Nat.cast_nonneg _
    have hprod : (q : ℝ) * scale ≤
        (4 * (65536 * (L : ℝ) ^ 3) * cycleFactor q) * scale := by
      have hh := hthreshold.trans (mul_le_mul_of_nonneg_left hsmall.le
        (by positivity : (0 : ℝ) ≤ 4 * cycleFactor q))
      nlinarith only [hh]
    have hcount := le_of_mul_le_mul_right hprod hscale
    have hfixed : (q : ℝ) - 1 ≤ 48 * (65536 * (L : ℝ) ^ 3) * cycleFactor q := by
      nlinarith [mul_nonneg hM hH]
    have hfactor := small_count_cycleFactor_le L q hL hqpos hfixed
    calc
      paid ≤ 2 * q * scale := hpaid
      _ ≤ 8 * cycleFactor q * treeCost := by nlinarith only [hthreshold]
      _ ≤ 288 * cycleFactor L * treeCost := by
        have hh := mul_le_mul_of_nonneg_right hfactor hcost
        nlinarith only [hh]

end OnlineSteinerForest.UpperBound
