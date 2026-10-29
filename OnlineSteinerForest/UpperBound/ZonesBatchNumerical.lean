import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Combining the small-tree and retained-pair estimates for one cost batch. -/
namespace OnlineSteinerForest.UpperBound

theorem single_batch_payment_budget (L H small retained count reference saving marks scale : ℝ)
    (hH : 1 ≤ H) (href : 0 ≤ reference)
    (hsmall : small ≤ 288 * H * reference)
    (hpaid : retained ≤ 2 * count * scale)
    (hcount : count * scale ≤ 32 * L * saving + 2 ^ 24 * L ^ 4 * marks * scale +
      2 ^ 28 * H * reference) :
    small + retained ≤ 64 * L * saving + 2 ^ 30 * H * reference +
      2 ^ 25 * L ^ 4 * marks * scale := by
  have hHr : 0 ≤ H * reference := mul_nonneg (by linarith) href
  nlinarith only [hsmall, hpaid, hcount, hHr]

end OnlineSteinerForest.UpperBound
