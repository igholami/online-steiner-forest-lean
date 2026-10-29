import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Exact numerical conversion of core saving and sparse discard budgets. -/
namespace OnlineSteinerForest.UpperBound

theorem replacement_count_budget (L H retained core reference saving coreCost marks scale : ℝ)
    (hL : 0 ≤ L)
    (hdiscard : (retained - core) * scale ≤ 2 ^ 28 * H * reference)
    (hcore : core * scale ≤ 16 * L * coreCost)
    (hsaving : coreCost / 2 - 2 ^ 19 * L ^ 3 * marks * scale ≤ saving) :
    retained * scale ≤ 32 * L * saving + 2 ^ 24 * L ^ 4 * marks * scale +
      2 ^ 28 * H * reference := by
  have hh := mul_le_mul_of_nonneg_left hsaving (by positivity : (0 : ℝ) ≤ 32 * L)
  nlinarith only [hh, hcore, hdiscard]

end OnlineSteinerForest.UpperBound
