import OnlineSteinerForest.UpperBound.GirthCollision
import OnlineSteinerForest.UpperBound.GirthPathTrace
import OnlineSteinerForest.UpperBound.GirthShortWalks

/-! The minimum-degree-three bound as a witness that survives graph reductions. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem minimum_degree_collision (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hC : 0 < ∑ i, w i) (n : ℕ) (hn : 2 * (Fintype.card V : ℝ) < (2 : ℝ) ^ n) :
    ∃ p : Collision left right, p.cost w ≤ 4 * (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I := by
  obtain ⟨p, q, hne, hp, hq, hf, hl, hcost⟩ :=
    two_short_nonbacktracking_walks left right hdegree w hw hC n hn
  have hqvalid : TraceValid left right (tail left right (first n p))
      (head left right (last n p)) (dartTrace n q) := by
    rw [hf, hl]
    exact dartTrace_valid left right n q hq
  let C : Collision left right := {
    start := tail left right (first n p)
    finish := head left right (last n p)
    firstTrace := dartTrace n p
    secondTrace := dartTrace n q
    firstValid := dartTrace_valid left right n p hp
    secondValid := hqvalid
    firstNonbacktracking := dartTrace_nonbacktracking left right n p hp
    secondNonbacktracking := dartTrace_nonbacktracking left right n q hq
    distinct := fun hh => hne (dartTrace_injective n hh) }
  exact ⟨C, by simpa only [Collision.cost, C, dartTrace_cost] using hcost⟩

theorem minimum_degree_collision_nonneg (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (n : ℕ) (hn : 2 * (Fintype.card V : ℝ) < (2 : ℝ) ^ n) :
    ∃ p : Collision left right, p.cost w ≤ 4 * (n + 1 : ℕ) * (∑ i, w i) / Fintype.card I := by
  by_cases hC : 0 < ∑ i, w i
  · exact minimum_degree_collision left right hdegree w hw hC n hn
  · have hzero : ∑ i, w i = 0 := le_antisymm (le_of_not_gt hC)
      (Finset.sum_nonneg (by intro i _; exact hw i))
    have hwzero : w = fun _ => 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff_of_nonneg (by intro i _; exact hw i)).mp hzero i (Finset.mem_univ i)
    obtain ⟨p, _⟩ := minimum_degree_collision left right hdegree (fun _ => 1)
      (by intro; norm_num) (by simp; positivity) n hn
    exact ⟨p, by simp [hwzero, Collision.cost, traceCost]⟩

end OnlineSteinerForest.UpperBound.Girth
