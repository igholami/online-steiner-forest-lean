import OnlineSteinerForest.LowerBound.Parameters
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-! Elementary power estimates at the manuscript's lower-bound parameter range. -/
namespace OnlineSteinerForest.LowerBound

theorem scaled_linear_le_power (h : ℕ) (hh : 32 ≤ h) : 1024 * h ≤ 2 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

theorem scaled_linear_le_half_power (h : ℕ) (hh : 32 ≤ h) :
    512 * h ≤ 2 ^ (h / 2) := by
  have hg : ∀ n : ℕ, 16 ≤ n → 512 * (2 * n + 1) ≤ 2 ^ n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih => rw [pow_succ]; omega
  have hhalf : 16 ≤ h / 2 := by omega
  have hb := hg (h / 2) hhalf
  omega

theorem prefixFraction_pos (h : ℕ) (hh : 0 < h) : 0 < prefixFraction h := by
  unfold prefixFraction
  exact div_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hh))
    (Nat.cast_pos.mpr (logSize_pos h))

theorem prefixFraction_le_quarter (h : ℕ) (hh : 32 ≤ h) : prefixFraction h ≤ 1 / 4 := by
  have hpow : (1024 : ℚ) * h ≤ logSize h := by
    exact_mod_cast scaled_linear_le_power h hh
  unfold prefixFraction
  apply (div_le_iff₀ (Nat.cast_pos.mpr (logSize_pos h))).mpr
  norm_num at hpow ⊢
  linarith

/-- Enough room in the original path for all short alternate-path patterns. -/
theorem power_ge_four_sq_add_two (n : ℕ) (hn : 16 ≤ n) : 4 * n ^ 2 + 2 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hquad : 3 * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
    rw [pow_succ 2 n]
    nlinarith

end OnlineSteinerForest.LowerBound
