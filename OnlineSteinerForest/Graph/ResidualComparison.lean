import OnlineSteinerForest.Graph.Residual

/-! Compare residual path costs with costs in an auxiliary graph. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [DecidableEq V]

theorem residualCost_eq_sum (c : Sym2 V → ℝ) (B F : Finset (Sym2 V)) :
    residualCost c B F = ∑ e ∈ F, if e ∈ B then 0 else c e := by
  classical
  simp [residualCost, Finset.sdiff_eq_filter, Finset.sum_filter]

/-- Auxiliary prices may be lower than actual residual prices, including on free edges. -/
theorem edgeCost_le_residualCost (c d : Sym2 V → ℝ) (B F : Finset (Sym2 V))
    (hfree : ∀ e ∈ F, e ∈ B → d e ≤ 0)
    (hpaid : ∀ e ∈ F, e ∉ B → d e ≤ c e) :
    edgeCost d F ≤ residualCost c B F := by
  rw [residualCost_eq_sum]
  apply Finset.sum_le_sum
  intro e he
  split_ifs with h
  · exact hfree e he h
  · exact hpaid e he h

end OnlineSteinerForest
