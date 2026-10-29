import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! A rational sampling parameter suffices for the dense-core domination bound. -/
namespace OnlineSteinerForest.UpperBound

/-- Sampling with probability `1/1024` misses any set of size at least `8192`
with probability at most `1/1024`. -/
theorem replacement_miss_probability_le (n : ℕ) (hn : 8192 ≤ n) :
    (1 - (1 / 1024 : ℝ)) ^ n ≤ 1 / 1024 := by
  have he1 : (5 / 2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.quadratic_le_exp_of_nonneg (x := 1) (by norm_num)
    norm_num at h
    exact h
  have he8 : (1024 : ℝ) ≤ Real.exp 8 := by
    calc
      _ ≤ (5 / 2 : ℝ) ^ 8 := by norm_num
      _ ≤ (Real.exp 1) ^ 8 := pow_le_pow_left₀ (by norm_num) he1 8
      _ = _ := by simpa using (Real.exp_nat_mul 1 8).symm
  have hinv : Real.exp (-8) ≤ 1 / 1024 := by
    simpa only [Real.exp_neg, one_div] using
      one_div_le_one_div_of_le (show (0 : ℝ) < 1024 by norm_num) he8
  calc
    _ ≤ (1 - (1 / 1024 : ℝ)) ^ 8192 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    _ ≤ (Real.exp (-(1 / 1024 : ℝ))) ^ 8192 :=
      pow_le_pow_left₀ (by norm_num) (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-8) := by rw [← Real.exp_nat_mul]; congr 1; norm_num
    _ ≤ _ := hinv

end OnlineSteinerForest.UpperBound
