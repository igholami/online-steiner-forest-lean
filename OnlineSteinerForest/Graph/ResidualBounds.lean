import OnlineSteinerForest.Graph.ResidualComparison

/-! Monotonicity in path edges and subadditivity of residual purchase costs. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [DecidableEq V]

theorem residualCost_mono_edges (c : Sym2 V → ℝ) (B F H : Finset (Sym2 V))
    (hFH : F ⊆ H) (hc : ∀ e ∈ H, 0 ≤ c e) : residualCost c B F ≤ residualCost c B H := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    obtain ⟨heF, heB⟩ := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr ⟨hFH heF, heB⟩
  · intro e he _
    exact hc e (Finset.mem_sdiff.mp he).1

theorem residualCost_union_le (c : Sym2 V → ℝ) (B F H : Finset (Sym2 V))
    (hc : ∀ e ∈ H, 0 ≤ c e) :
    residualCost c B (F ∪ H) ≤ residualCost c B F + residualCost c B H := by
  classical
  let d := fun e => if e ∈ B then (0 : ℝ) else c e
  simp only [residualCost_eq_sum]
  change edgeCost d (F ∪ H) ≤ edgeCost d F + edgeCost d H
  rw [edgeCost_union]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
  intro e he _
  dsimp [d]
  split_ifs
  · exact le_rfl
  · exact hc e he

end OnlineSteinerForest
