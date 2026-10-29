import OnlineSteinerForest.UpperBound.GirthZeroCost
import OnlineSteinerForest.UpperBound.GirthComponents
import OnlineSteinerForest.UpperBound.GirthDegreeSum
import OnlineSteinerForest.UpperBound.GirthLength

/-! The manuscript cycle-rank bound for the degree-three kernel. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem kernel_cycle_rank_bound (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hr : 1 ≤ cycleRank left right) :
    ∃ z, ∃ c : (edgeSubdivision left right).Walk z z, c.IsCycle ∧
      (c.edges.map (subdivisionCost w)).sum ≤
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
  have hrm : r ≤ Fintype.card I := by
    have hh := componentCount_le_vertices left right
    omega
  obtain ⟨z, c, hc, hcost⟩ := minimum_degree_short_cycle_nonneg left right hdegree w hw
    ⌈Real.logb 2 (8 * r : ℝ)⌉₊ (rank_length_dominates_vertices r _ hr hv)
  refine ⟨z, c, hc, hcost.trans ?_⟩
  change 4 * (cycleFactor r : ℝ) * (∑ i, w i) / Fintype.card I ≤ _
  have hC : 0 ≤ ∑ i, w i := Finset.sum_nonneg (by intro i _; exact hw i)
  exact div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast hr)
    (Nat.cast_le.mpr hrm)

end OnlineSteinerForest.UpperBound.Girth
