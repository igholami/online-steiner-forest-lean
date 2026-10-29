import OnlineSteinerForest.UpperBound.AuxiliaryHelpful

/-! Actual helpful pairs stay free in every later greedy residual metric. -/
namespace OnlineSteinerForest.UpperBound.HelpfulAt

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {c : Sym2 V → ℝ} {requests : List (V × V)}
  {feasible : ∀ q ∈ requests, G.Reachable q.1 q.2}
  {i : Fin requests.length} {scale : ℝ} {out : AuxiliaryOutput V}

theorem before_zero_of_lt (h : HelpfulAt G c requests feasible i scale out)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (j : ℕ) (hij : i.val < j) :
    residualDistance G c (boughtBefore G c requests feasible j) out.left out.right h.reachable = 0 := by
  apply le_antisymm
  · exact (residualDistance_antitone G c hc _ _
      (boughtBefore_mono G c requests feasible (i.val + 1) j (by omega))
      out.left out.right h.reachable).trans_eq h.bought_zero
  · exact residualDistance_nonneg G c hc _ _ _ _

end OnlineSteinerForest.UpperBound.HelpfulAt
