import OnlineSteinerForest.UpperBound.GirthMarkovPaths

/-! Expected accumulated cost of a finite stationary Markov path. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {D : Type*} [Fintype D]

theorem weighted_path_cost (T : D → D → ℝ) (hrow : ∀ d, ∑ e, T d e = 1)
    (hcolumn : ∀ e, ∑ d, T d e = 1) (c : ℝ) (w : D → ℝ) (n : ℕ) :
    (∑ p : Paths D n, pathWeight (fun _ => c) T n p * pathCost w n p) =
      (n + 1 : ℕ) * c * ∑ d, w d := by
  induction n with
  | zero =>
    simp only [Nat.cast_add, Nat.cast_zero, Nat.cast_one, zero_add, one_mul]
    change (∑ d : D, c * w d) = c * ∑ d : D, w d
    rw [Finset.mul_sum]
  | succ n ih =>
    have hnew := weighted_terminal_sum T hcolumn c (n + 1) w
    change (∑ p : Paths D n × D, pathWeight (fun _ => c) T n p.1 *
      T (last n p.1) p.2 * w p.2) = c * ∑ d, w d at hnew
    have hold : (∑ p : Paths D n × D, pathWeight (fun _ => c) T n p.1 *
        T (last n p.1) p.2 * pathCost w n p.1) =
        ∑ p : Paths D n, pathWeight (fun _ => c) T n p * pathCost w n p := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p _
      calc
        _ = (pathWeight (fun _ => c) T n p * pathCost w n p) * ∑ e, T (last n p) e := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro e _
          ring
        _ = _ := by rw [hrow, mul_one]
    change (∑ p : Paths D n × D, pathWeight (fun _ => c) T n p.1 *
      T (last n p.1) p.2 * (pathCost w n p.1 + w p.2)) = _
    calc
      _ = (∑ p : Paths D n × D, pathWeight (fun _ => c) T n p.1 *
          T (last n p.1) p.2 * pathCost w n p.1) +
          (∑ p : Paths D n × D, pathWeight (fun _ => c) T n p.1 * T (last n p.1) p.2 * w p.2) := by
        simp only [mul_add, Finset.sum_add_distrib]
      _ = (∑ p : Paths D n, pathWeight (fun _ => c) T n p * pathCost w n p) + c * ∑ d, w d := by
        rw [hold, hnew]
      _ = _ := by rw [ih]; push_cast; ring

end OnlineSteinerForest.UpperBound.Girth
