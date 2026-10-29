import OnlineSteinerForest.LowerBound.Parameters
import Lean.Elab.Tactic.Omega

/-! Exact size identities, including the evenness of the original vertex count. -/
namespace OnlineSteinerForest.LowerBound

theorem twice_matchingSize (h : ℕ) : 2 * matchingSize h = vertexCount h := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (logSize_pos h).ne'
  simp only [matchingSize, vertexCount, hk, pow_succ]
  rw [Nat.mul_div_cancel] <;> omega

theorem two_mul_le_power (n : ℕ) (hn : 0 < n) : 2 * n ≤ 2 ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [pow_succ]; omega

theorem logSize_le_matchingSize (h : ℕ) : logSize h ≤ matchingSize h := by
  have hp := two_mul_le_power (logSize h) (logSize_pos h)
  change 2 * logSize h ≤ vertexCount h at hp
  rw [← twice_matchingSize] at hp
  omega

end OnlineSteinerForest.LowerBound
