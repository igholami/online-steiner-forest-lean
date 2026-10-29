import OnlineSteinerForest.UpperBound.GirthCollisionPaths
import Mathlib.Tactic.FieldSimp

/-! A weighted Moore bound stated directly for a finite labelled multigraph. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem collision_size_of_vertex_bound (n : ℕ)
    (hn : 2 * (Fintype.card V : ℝ) < (2 : ℝ) ^ n) :
    (Fintype.card (Dart I × V) : ℝ) *
      ((1 / (Fintype.card (Dart I) : ℝ)) * (1 / 2 : ℝ) ^ n) < 1 / 2 := by
  have hd : (Fintype.card (Dart I) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Fintype.card_prod, Nat.cast_mul]
  have heq : (Fintype.card (Dart I) : ℝ) * (Fintype.card V : ℝ) *
      ((1 / (Fintype.card (Dart I) : ℝ)) * (1 / 2 : ℝ) ^ n) =
      (Fintype.card V : ℝ) / (2 : ℝ) ^ n := by
    rw [div_pow]
    simp only [one_pow]
    field_simp
  rw [heq]
  exact (div_lt_iff₀ (by positivity)).mpr (by linarith)

/-- Two distinct nonbacktracking walks have the same first oriented edge and last vertex,
with total weight at most four times their stationary mean. Loops and parallel labels are allowed. -/
theorem two_short_nonbacktracking_walks (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hC : 0 < ∑ i, w i) (n : ℕ)
    (hn : 2 * (Fintype.card V : ℝ) < (2 : ℝ) ^ n) :
    ∃ p q : Paths (Dart I) n,
      p ≠ q ∧ Nonbacktracking left right n p ∧ Nonbacktracking left right n q ∧
      first n p = first n q ∧ head left right (last n p) = head left right (last n q) ∧
      walkCost w n p + walkCost w n q ≤
        4 * (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I := by
  let B : ℝ := (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I
  have hm : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hB : 0 < B := div_pos (mul_pos (by exact_mod_cast Nat.succ_pos n) hC) hm
  have hmean : (n + 1 : ℕ) * (1 / (Fintype.card (Dart I) : ℝ)) * (2 * ∑ i, w i) ≤ B := by
    dsimp [B]
    rw [show Fintype.card (Dart I) = Fintype.card I * 2 by simp [Dart]]
    push_cast
    field_simp
    norm_num
  obtain ⟨p, q, hpq, hp, hq, hf, hl, hpc, hqc⟩ := exists_short_collision
    left right hdegree w hw n B hB hmean (collision_size_of_vertex_bound n hn)
  refine ⟨p, q, hpq, hp, hq, hf, hl, ?_⟩
  have heq : 4 * B = 4 * (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I := by dsimp [B]; ring
  rw [← heq]
  linarith

end OnlineSteinerForest.UpperBound.Girth
