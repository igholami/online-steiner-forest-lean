import OnlineSteinerForest.UpperBound.GirthMinimumCollision
import OnlineSteinerForest.UpperBound.GirthKernelBound
import OnlineSteinerForest.UpperBound.GirthConnectedRank

/-! The degree-three induction base at the manuscript's exact cycle-rank bound. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem kernel_collision_rank_bound (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hr : 1 ≤ cycleRank left right) :
    ∃ p : Collision left right, p.cost w ≤
      4 * cycleFactor (cycleRank left right) * (∑ i, w i) / cycleRank left right := by
  let r := cycleRank left right
  have hrank : Fintype.card I + componentCount left right = Fintype.card V + r := by
    have hh : 3 * Fintype.card V ≤ 2 * Fintype.card I := by
      calc
        _ = ∑ _v : V, 3 := by simp [Nat.mul_comm]
        _ ≤ ∑ v, degree left right v := Finset.sum_le_sum (by intro v _; exact hdegree v)
        _ = _ := degree_sum left right
    dsimp [r, cycleRank]
    omega
  have hv := minimum_degree_vertex_bound left right hdegree r (componentCount left right) hrank
  obtain ⟨p, hp⟩ := minimum_degree_collision_nonneg left right hdegree w hw
    ⌈Real.logb 2 (8 * r : ℝ)⌉₊ (rank_length_dominates_vertices r _ hr hv)
  refine ⟨p, hp.trans ?_⟩
  change 4 * (cycleFactor r : ℝ) * (∑ i, w i) / Fintype.card I ≤ _
  have hC : 0 ≤ ∑ i, w i := Finset.sum_nonneg (by intro i _; exact hw i)
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hr)
    (Nat.cast_le.mpr (cycleRank_le_edgeCount left right))

end OnlineSteinerForest.UpperBound.Girth
