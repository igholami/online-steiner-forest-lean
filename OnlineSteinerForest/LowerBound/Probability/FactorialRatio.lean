import Mathlib.Data.Nat.Factorial.Basic
import OnlineSteinerForest.Graph.Cost
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-! A small prescribed tuple loses at most a factor two versus independent images. -/
namespace OnlineSteinerForest.LowerBound.Probability

/-- A union-bound lower estimate for the falling factorial, proved from its recurrence. -/
theorem descFactorial_lower (N k : ℕ) :
    (2 * (N : ℝ) - (k : ℝ) * ((k : ℝ) - 1)) * (N : ℝ) ^ k ≤
      2 * (N : ℝ) * N.descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlow := mul_le_mul_of_nonneg_left ih (show (0 : ℝ) ≤ N from Nat.cast_nonneg _)
    have hupper : (N.descFactorial k : ℝ) ≤ (N : ℝ) ^ k := by
      exact_mod_cast Nat.descFactorial_le_pow N k
    have hu := mul_le_mul_of_nonneg_left hupper
      (show (0 : ℝ) ≤ 2 * (N : ℝ) * k by positivity)
    have hrec : (N.descFactorial (k + 1) : ℝ) + (k : ℝ) * N.descFactorial k =
        (N.descFactorial k : ℝ) * N := by
      exact_mod_cast (Nat.descFactorial_mul_self N k).symm
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

/-- For `k² ≤ N`, at least half of all tuples of length `k` are injective. -/
theorem half_power_le_descFactorial (N k : ℕ) (hN : 0 < N) (hk : k ^ 2 ≤ N) :
    (N : ℝ) ^ k / 2 ≤ N.descFactorial k := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hk' : (k : ℝ) ^ 2 ≤ N := by exact_mod_cast hk
  have hc : (N : ℝ) ≤ 2 * N - (k : ℝ) * ((k : ℝ) - 1) := by
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hN'.le k)
  have hl := descFactorial_lower N k
  have hi : (N : ℝ) * (N : ℝ) ^ k ≤ (N : ℝ) * (2 * N.descFactorial k) := by
    nlinarith
  have hd := le_of_mul_le_mul_left hi hN'
  linarith

theorem factorial_ratio_le (N k : ℕ) (hN : 0 < N) (hk : k ^ 2 ≤ N) :
    ((N - k).factorial : ℝ) / N.factorial ≤ 2 / (N : ℝ) ^ k := by
  have hkN : k ≤ N := by
    by_cases hk0 : k = 0
    · omega
    · have hkk : k ≤ k ^ 2 := by
        have hh := Nat.mul_le_mul_left k (show 1 ≤ k by omega)
        simpa only [mul_one, pow_two] using hh
      exact hkk.trans hk
  have hf : (N.factorial : ℝ) = ((N - k).factorial : ℝ) * N.descFactorial k := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hkN).symm
  have hrem : (0 : ℝ) < (N - k).factorial := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hD : (0 : ℝ) < N.descFactorial k := Nat.cast_pos.mpr (Nat.descFactorial_pos.mpr hkN)
  have hpow : (0 : ℝ) < (N : ℝ) ^ k := pow_pos (Nat.cast_pos.mpr hN) _
  calc
    _ = 1 / (N.descFactorial k : ℝ) := by rw [hf]; field_simp
    _ ≤ _ := (div_le_div_iff₀ hD hpow).mpr (by linarith [half_power_le_descFactorial N k hN hk])

end OnlineSteinerForest.LowerBound.Probability
