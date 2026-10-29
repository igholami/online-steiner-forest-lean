import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The final numerical accounting step of Section 4, isolated from graph lemmas.
This is a conditional arithmetic lemma, not the upper-bound theorem. -/
namespace OnlineSteinerForest.UpperBound

/-- Absorb the omitted `ALG / 32` payments exactly as in the manuscript. -/
theorem absorb_omissions (ALG OPT L M A : ℝ)
    (h : ALG ≤ OPT + ALG / 32 + 64 * M * L * OPT + A * L * OPT) :
    ALG ≤ (32 / 31 : ℝ) * OPT * (1 + 64 * M * L + A * L) := by
  nlinarith

/-- Monotone reference costs telescope to at most their initial cost. -/
theorem total_savings_le_initial (cost : ℕ → ℝ) (n : ℕ)
    (hnonneg : 0 ≤ cost n) :
    (∑ i ∈ Finset.range n, (cost i - cost (i + 1))) ≤ cost 0 := by
  have ht : (∑ i ∈ Finset.range n, (cost i - cost (i + 1))) = cost 0 - cost n := by
    clear hnonneg
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  rw [ht]
  linarith

/-- Add the batch bounds, then use the total savings budget and state-cost budget. -/
theorem sum_batch_bounds {ι : Type*} (batches : Finset ι)
    (payment saving reference : ι → ℝ) (L A savingsBudget referenceBudget : ℝ)
    (hL : 0 ≤ L) (hA : 0 ≤ A)
    (hbatch : ∀ b ∈ batches, payment b ≤ 64 * L * saving b + A * reference b)
    (hsave : ∑ b ∈ batches, saving b ≤ savingsBudget)
    (href : ∑ b ∈ batches, reference b ≤ referenceBudget) :
    ∑ b ∈ batches, payment b ≤ 64 * L * savingsBudget + A * referenceBudget := by
  calc
    ∑ b ∈ batches, payment b ≤
        ∑ b ∈ batches, (64 * L * saving b + A * reference b) :=
      Finset.sum_le_sum hbatch
    _ = 64 * L * (∑ b ∈ batches, saving b) + A * (∑ b ∈ batches, reference b) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hsave (by positivity))
      (mul_le_mul_of_nonneg_left href hA)

end OnlineSteinerForest.UpperBound
