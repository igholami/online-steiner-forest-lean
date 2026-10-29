import OnlineSteinerForest.UpperBound.GirthMarkovPaths
import Mathlib.Tactic.Positivity

/-! Normalization and atom bounds for finite nonbacktracking path probabilities. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {D : Type*} [Fintype D]

theorem pathWeight_le_half_power (T : D → D → ℝ) (hT0 : ∀ d e, 0 ≤ T d e)
    (hT : ∀ d e, T d e ≤ 1 / 2) (c : ℝ) (hc : 0 ≤ c) (n : ℕ) (p : Paths D n) :
    pathWeight (fun _ => c) T n p ≤ c * (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp [pathWeight]
  | succ n ih =>
    change pathWeight (fun _ => c) T n p.1 * T (last n p.1) p.2 ≤ _
    calc
      _ ≤ (c * (1 / 2 : ℝ) ^ n) * (1 / 2) :=
        mul_le_mul (ih p.1) (hT _ _) (hT0 _ _) (by positivity)
      _ = _ := by rw [pow_succ]; ring

theorem sum_uniform_pathWeight [Nonempty D] (T : D → D → ℝ) (hcolumn : ∀ e, ∑ d, T d e = 1)
    (n : ℕ) : (∑ p : Paths D n, pathWeight (fun _ => 1 / (Fintype.card D : ℝ)) T n p) = 1 := by
  have hh := weighted_terminal_sum T hcolumn (1 / (Fintype.card D : ℝ)) n (fun _ => 1)
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hh
  have hcard : (Fintype.card D : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simpa [hcard] using hh

end OnlineSteinerForest.UpperBound.Girth
