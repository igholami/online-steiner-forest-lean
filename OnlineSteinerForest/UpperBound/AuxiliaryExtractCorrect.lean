import OnlineSteinerForest.UpperBound.AuxiliaryProxyHelpful

/-! The actual extraction implementation returns only certified helpful outputs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem extractLabelAux_helpful (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (scale : ℝ) (hs : 0 ≤ scale)
    (hbatch : ∀ i ∈ batch, scale ≤ payment G c requests feasible i ∧ payment G c requests feasible i ≤ 2 * scale)
    (j : Fin (n + 1)) (out : AuxiliaryOutput V)
    (hout : extractLabelAux G c hc requests feasible fallback batch label hcard scale j = some out) :
    HelpfulAt G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard j) scale out := by
  have hm := Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard j)
  have hband := hbatch _ hm.1
  dsimp only [extractLabelAux] at hout
  split_ifs at hout with hcheap hzero hlong
  · have heq := Option.some.inj hout
    subst out
    apply directAuxOutput_helpful G c hc requests feasible _ hm.2.1 scale hs hband.1 hband.2
    right
    simpa only [hm.2.2.2] using hcheap
  · have heq := Option.some.inj hout
    subst out
    have hp := proxyAuxOutput_helpful G c hc requests feasible fallback batch label hcard
      (predecessorPosition j hzero) scale
      (by simpa only [newIndex_predecessorPosition] using hband.1) (le_of_not_gt hlong)
    simpa only [newIndex_predecessorPosition] using hp

end OnlineSteinerForest.UpperBound
