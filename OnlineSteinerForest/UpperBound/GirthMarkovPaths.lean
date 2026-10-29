import OnlineSteinerForest.Graph.Cost
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Ring

/-! Finite nonbacktracking path probabilities, before specializing to graph darts. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {D : Type*}

def Paths (D : Type*) : ℕ → Type _
  | 0 => D
  | n + 1 => Paths D n × D

attribute [reducible] Paths

instance pathsFintype [Fintype D] (n : ℕ) : Fintype (Paths D n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype D)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Paths D n × D))

def first : (n : ℕ) → Paths D n → D
  | 0, p => p
  | n + 1, p => first n p.1

def last : (n : ℕ) → Paths D n → D
  | 0, p => p
  | _ + 1, p => p.2

attribute [reducible] first last

noncomputable def pathWeight (initial : D → ℝ) (T : D → D → ℝ) : (n : ℕ) → Paths D n → ℝ
  | 0, p => initial p
  | n + 1, p => pathWeight initial T n p.1 * T (last n p.1) p.2

noncomputable def pathCost (w : D → ℝ) : (n : ℕ) → Paths D n → ℝ
  | 0, p => w p
  | n + 1, p => pathCost w n p.1 + w p.2

variable [Fintype D]

/-- Column sums one imply stationarity of the uniform state weights at every time. -/
theorem weighted_terminal_sum (T : D → D → ℝ) (hcolumn : ∀ e, ∑ d, T d e = 1)
    (c : ℝ) (n : ℕ) (f : D → ℝ) :
    (∑ p : Paths D n, pathWeight (fun _ => c) T n p * f (last n p)) = c * ∑ d, f d := by
  induction n generalizing f with
  | zero =>
    change (∑ d : D, c * f d) = c * ∑ d : D, f d
    rw [Finset.mul_sum]
  | succ n ih =>
    change (∑ p : Paths D n × D,
      pathWeight (fun _ => c) T n p.1 * T (last n p.1) p.2 * f p.2) = _
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ p : Paths D n, pathWeight (fun _ => c) T n p *
          (∑ e : D, T (last n p) e * f e) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
      _ = c * ∑ d : D, ∑ e : D, T d e * f e := ih (fun d => ∑ e : D, T d e * f e)
      _ = c * ∑ e : D, (∑ d : D, T d e) * f e := by
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ = _ := by simp only [hcolumn, one_mul]

theorem pathWeight_nonneg (initial : D → ℝ) (T : D → D → ℝ)
    (hinit : ∀ d, 0 ≤ initial d) (hT : ∀ d e, 0 ≤ T d e)
    (n : ℕ) (p : Paths D n) : 0 ≤ pathWeight initial T n p := by
  induction n with
  | zero => exact hinit p
  | succ n ih => exact mul_nonneg (ih p.1) (hT _ _)

end OnlineSteinerForest.UpperBound.Girth
