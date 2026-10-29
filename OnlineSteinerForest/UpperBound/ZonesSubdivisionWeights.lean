import Mathlib.Algebra.Order.Archimedean.Real.Basic
import OnlineSteinerForest.Graph.Cost
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! A common finite segment count makes every positive input edge short enough. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

/-- One common segment count suffices for every edge in a finite reference graph. -/
theorem exists_uniform_subdivision_count {E : Type*} [Fintype E]
    (c : E → ℝ) (M : ℝ) (hM : 0 < M) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ e, c e / (B : ℝ) ≤ M := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((∑ e, max (c e) 0) / M)
  let B := n + 2
  have hB : (0 : ℝ) < B := by dsimp [B]; positivity
  refine ⟨B, by omega, ?_⟩
  intro e
  have he : c e ≤ ∑ f, max (c f) 0 := by
    exact (le_max_left _ _).trans (Finset.single_le_sum (fun _ _ => le_max_right _ _) (Finset.mem_univ e))
  have hn' := (div_lt_iff₀ hM).mp hn
  apply (div_le_iff₀ hB).mpr
  have hnB : (n : ℝ) ≤ B := by dsimp [B]; norm_num
  nlinarith

/-- Equal positive segments have precisely the original total edge cost. -/
theorem uniform_segment_sum (a : ℝ) (B : ℕ) (hB : B ≠ 0) :
    (∑ _ : Fin B, a / (B : ℝ)) = a := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- Repeated halving eventually makes every segment shorter than the target. -/
theorem exists_binary_subdivision_depth (C M : ℝ) (hM : 0 < M) :
    ∃ n : ℕ, C / (2 : ℝ) ^ n ≤ M := by
  obtain ⟨n, hn⟩ := exists_nat_gt (C / M)
  have hp : (n : ℝ) < (2 : ℝ) ^ n := by exact_mod_cast n.lt_two_pow_self
  have hC := (div_lt_iff₀ hM).mp hn
  refine ⟨n, (div_le_iff₀ (by positivity)).mpr ?_⟩
  nlinarith

end OnlineSteinerForest.UpperBound
