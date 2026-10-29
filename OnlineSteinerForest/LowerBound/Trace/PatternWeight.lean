import OnlineSteinerForest.LowerBound.Probability.Patterns

/-! Exponential pattern weight is at least one precisely for cheap routes. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable [OnlineSteinerForest.PathSelection]

open Probability

theorem pattern_weight_eq {h : ℕ} {i : Fin (matchingSize h)} {q : ℕ}
    (p : RawPattern h i q) (D S : ℝ)
    (hD : (∑ j : Fin (q + 1), (((p.runs j).1.val + 1 : ℕ) : ℝ)) = D)
    (hS : (∑ j : Fin q, testPrice h i (p.ranks j).val) = S) :
    p.weight = Real.exp (16 * rankFraction h i * (rankPrice h i - D - S)) := by
  unfold RawPattern.weight shortcutWeight
  rw [← Real.exp_sum, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [← Finset.mul_sum, ← Finset.mul_sum, hD, hS]
  ring

theorem pattern_weight_ge_one {h : ℕ} {i : Fin (matchingSize h)} {q : ℕ}
    (p : RawPattern h i q) (D S : ℝ)
    (hD : (∑ j : Fin (q + 1), (((p.runs j).1.val + 1 : ℕ) : ℝ)) = D)
    (hS : (∑ j : Fin q, testPrice h i (p.ranks j).val) = S)
    (hcheap : D + S ≤ rankPrice h i) : 1 ≤ p.weight := by
  rw [pattern_weight_eq p D S hD hS]
  have hnonneg : 0 ≤ 16 * rankFraction h i * (rankPrice h i - D - S) :=
    mul_nonneg (le_of_lt (mul_pos (by norm_num) (rankFraction_pos h i))) (by linarith)
  simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hnonneg

end OnlineSteinerForest.LowerBound.Trace
