import OnlineSteinerForest.UpperBound.AuxiliaryExtractLabel

/-! Every computed omission is one of the budgeted first or long cases. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extractLabelAux_none_cases (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (scale : ℝ) (j : Fin (n + 1))
    (hn : extractLabelAux G c hc requests feasible fallback batch label hcard scale j = none) :
    j ∈ firstLabelPositions G c requests feasible batch label hcard ∨
      ∃ k ∈ longLabelPositions G c hc requests feasible fallback batch label hcard scale, newIndex k = j := by
  dsimp only [extractLabelAux] at hn
  split_ifs at hn with hcheap hzero hlong
  · left
    have hpay : blockPayment G c requests feasible
        (orderedLabelRequest G c requests feasible batch label hcard j).val =
        payment G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard j) := by
      simp only [blockPayment, dif_pos (orderedLabelRequest G c requests feasible batch label hcard j).isLt]
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_⟩
    · exact Finset.mem_singleton.mpr (Fin.ext hzero)
    · rw [hpay]
      exact lt_of_not_ge hcheap
  · right
    refine ⟨predecessorPosition j hzero, ?_, newIndex_predecessorPosition j hzero⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hlong, ?_⟩
    rw [newIndex_predecessorPosition]
    simpa only [blockPayment, dif_pos (orderedLabelRequest G c requests feasible batch label hcard j).isLt]
      using lt_of_not_ge hcheap

end OnlineSteinerForest.UpperBound
