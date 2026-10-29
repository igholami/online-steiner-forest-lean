import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Convert the constructed skeleton and attachment cost into the manuscript's exact core saving. -/
namespace OnlineSteinerForest.UpperBound

theorem dense_candidate_cost_saving (M N components marks coreCost keptCost candidateCost : ℝ)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hmarks : 0 ≤ marks)
    (hcomponents : 8192 * components ≤ N) (hcore : M * N ≤ coreCost)
    (hcandidate : candidateCost ≤ keptCost + (11 / 512 : ℝ) * M * N + 6 * M * (components + marks)) :
    candidateCost ≤ keptCost + coreCost / 2 + 8 * M * marks := by
  have hcount := mul_le_mul_of_nonneg_left hcomponents (by positivity : 0 ≤ 6 * M)
  have hMN := mul_nonneg hM hN
  have hmarked := mul_nonneg hM hmarks
  nlinarith

end OnlineSteinerForest.UpperBound
