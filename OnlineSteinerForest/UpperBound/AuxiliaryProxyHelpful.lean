import OnlineSteinerForest.UpperBound.AuxiliaryHelpful

/-! Every retained nearest-earlier proxy satisfies the helpful-output conditions. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem proxyAuxOutput_helpful (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) (scale : ℝ)
    (hlo : scale ≤ payment G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard (newIndex j)))
    (hlen : labelProxyLength G c hc requests feasible fallback batch label hcard j ≤
      256 * (cycleFactor requests.length : ℝ) ^ 3 * scale) :
    HelpfulAt G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard (newIndex j)) scale
      (proxyAuxOutput G c hc requests feasible fallback batch label hcard j) := by
  have hp := labelProxyEdges_spec G c hc requests feasible fallback batch label hcard j
  obtain ⟨hr, hsep, hzero⟩ := labelProxy_metric G c hc requests feasible fallback batch label hcard j
  refine ⟨hp.1, hr, ?_, hzero, ?_⟩
  · exact (by linarith : scale / 2 ≤ payment G c requests feasible
      (orderedLabelRequest G c requests feasible batch label hcard (newIndex j)) / 2).trans hsep
  · change edgeCost c (labelProxyEdges G c hc requests feasible fallback batch label hcard j) ≤ _
    rw [hp.2]
    exact hlen

end OnlineSteinerForest.UpperBound
