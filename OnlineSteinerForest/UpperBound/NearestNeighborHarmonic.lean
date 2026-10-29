import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-! The harmonic tail appearing when sorted insertion distances are summed. -/
namespace OnlineSteinerForest.UpperBound

theorem reciprocal_tail_sum_le_log (n : ℕ) :
    (∑ k ∈ Finset.range n, (((k + 2 : ℕ) : ℝ)⁻¹)) ≤ Real.log ((n + 1 : ℕ) : ℝ) := by
  have hh := harmonic_le_one_add_log (n + 1)
  rw [harmonic] at hh
  push_cast at hh
  rw [Finset.sum_range_succ'] at hh
  norm_num at hh
  simp only [add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] at hh
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  linarith


end OnlineSteinerForest.UpperBound
