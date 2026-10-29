import OnlineSteinerForest.UpperBound.GirthTransition
import OnlineSteinerForest.UpperBound.GirthMarkovCost
import OnlineSteinerForest.UpperBound.GirthMarkovBounds

/-! Stationary nonbacktracking paths in a labelled finite multigraph. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

def Nonbacktracking (left right : I → V) : (n : ℕ) → Paths (Dart I) n → Prop
  | 0, _ => True
  | n + 1, p => Nonbacktracking left right n p.1 ∧ p.2 ∈ successors left right (last n p.1)

attribute [reducible] Nonbacktracking

noncomputable def walkProbability (left right : I → V) (n : ℕ) (p : Paths (Dart I) n) : ℝ :=
  pathWeight (fun _ => 1 / (Fintype.card (Dart I) : ℝ)) (transition left right) n p

noncomputable def walkCost (w : I → ℝ) (n : ℕ) (p : Paths (Dart I) n) : ℝ :=
  pathCost (fun d => w d.1) n p

theorem walkProbability_nonneg (left right : I → V) (n : ℕ) (p : Paths (Dart I) n) :
    0 ≤ walkProbability left right n p :=
  pathWeight_nonneg _ _ (by intro; positivity) (transition_nonneg left right) n p

theorem positive_walkProbability_nonbacktracking (left right : I → V) (n : ℕ)
    (p : Paths (Dart I) n) (hp : 0 < walkProbability left right n p) :
    Nonbacktracking left right n p := by
  induction n with
  | zero => trivial
  | succ n ih =>
    change 0 < walkProbability left right n p.1 * transition left right (last n p.1) p.2 at hp
    have ha : 0 < walkProbability left right n p.1 :=
      (mul_pos_iff.mp hp).resolve_right (by intro h; exact (not_lt_of_ge (walkProbability_nonneg _ _ _ _)) h.1) |>.1
    have hb : p.2 ∈ successors left right (last n p.1) := by
      by_contra hn
      simp [transition, hn] at hp
    exact ⟨ih p.1 ha, hb⟩

theorem sum_walkProbability [Nonempty I] (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (n : ℕ) :
    (∑ p : Paths (Dart I) n, walkProbability left right n p) = 1 :=
  sum_uniform_pathWeight _ (transition_column_sum left right hdegree) n

theorem walkProbability_le (left right : I → V) (hdegree : ∀ v, 3 ≤ degree left right v)
    (n : ℕ) (p : Paths (Dart I) n) :
    walkProbability left right n p ≤ (1 / (Fintype.card (Dart I) : ℝ)) * (1 / 2 : ℝ) ^ n :=
  pathWeight_le_half_power _ (transition_nonneg left right) (transition_le_half left right hdegree)
    _ (by positivity) n p

theorem walkCost_nonneg (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (n : ℕ) (p : Paths (Dart I) n) :
    0 ≤ walkCost w n p := by
  induction n with
  | zero => exact hw p.1
  | succ n ih => exact add_nonneg (ih p.1) (hw p.2.1)

theorem expected_walkCost (left right : I → V) (hdegree : ∀ v, 3 ≤ degree left right v)
    (w : I → ℝ) (n : ℕ) :
    (∑ p : Paths (Dart I) n, walkProbability left right n p * walkCost w n p) =
      (n + 1 : ℕ) * (1 / (Fintype.card (Dart I) : ℝ)) * (2 * ∑ i, w i) := by
  unfold walkProbability walkCost
  rw [weighted_path_cost _ (transition_row_sum left right hdegree) (transition_column_sum left right hdegree)]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← two_mul, Finset.mul_sum]

end OnlineSteinerForest.UpperBound.Girth
