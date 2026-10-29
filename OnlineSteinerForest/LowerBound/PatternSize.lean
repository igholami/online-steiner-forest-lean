import OnlineSteinerForest.LowerBound.PowerEstimates
import Mathlib.Tactic.Ring

/-! The double-exponential vertex count dominates the finite pattern-counting errors. -/
namespace OnlineSteinerForest.LowerBound

theorem sixteen_mul_fourth_le_power (n : ℕ) (hn : 64 ≤ n) : 16 * n ^ 4 ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hlin : 16 * (n + 1) ≤ 17 * n := by omega
    have hpow := Nat.pow_le_pow_left hlin 4
    simp only [mul_pow] at hpow
    norm_num at hpow
    rw [pow_succ 2 n]
    omega

theorem logSize_ge_sixtyfour (h : ℕ) (hh : 32 ≤ h) : 64 ≤ logSize h := by
  have hp : (2 : ℕ) ^ 6 ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  exact hp

theorem vertexCount_ge_sixteen_fourth (h : ℕ) (hh : 32 ≤ h) :
    16 * (logSize h) ^ 4 ≤ vertexCount h :=
  sixteen_mul_fourth_le_power (logSize h) (logSize_ge_sixtyfour h hh)

theorem pattern_constraint_sq_le (h : ℕ) (hh : 32 ≤ h) (q : ℕ)
    (hq : q + 1 ≤ (logSize h) ^ 2) : (2 * q + 2) ^ 2 ≤ vertexCount h := by
  have hs : (2 * q + 2) ^ 2 ≤ (2 * (logSize h) ^ 2) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have ht := vertexCount_ge_sixteen_fourth h hh
  calc
    _ ≤ (2 * (logSize h) ^ 2) ^ 2 := hs
    _ = 4 * (logSize h) ^ 4 := by ring
    _ ≤ _ := by omega

end OnlineSteinerForest.LowerBound
