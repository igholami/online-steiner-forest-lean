import OnlineSteinerForest.UpperBound.AuxiliaryLabelProxy

/-! The computed nearest-earlier proxy has the required chronological residual geometry. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem labelProxy_metric (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) :
    let i := orderedLabelRequest G c requests feasible batch label hcard (newIndex j)
    let x := (labelFarSequence G c hc requests feasible fallback batch label hcard (newIndex j)).val
    let z := (labelFarSequence G c hc requests feasible fallback batch label hcard
      (labelProxyParent G c hc requests feasible fallback batch label hcard j)).val
    ∃ hr : G.Reachable x z,
      payment G c requests feasible i / 2 ≤ residualDistance G c
        (boughtBefore G c requests feasible i.val) x z hr ∧
      residualDistance G c (boughtBefore G c requests feasible (i.val + 1)) x z hr = 0 := by
  let k := labelProxyParent G c hc requests feasible fallback batch label hcard j
  let a := orderedLabelRequest G c requests feasible batch label hcard k
  let b := orderedLabelRequest G c requests feasible batch label hcard (newIndex j)
  have ha := (Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard k)).2
  have hb := (Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard (newIndex j))).2
  have hkj : k < newIndex j := by
    change (nearestEarlier _ _ _ _ j).val < j.val + 1
    exact (nearestEarlier _ _ _ _ j).isLt
  have hab : a.val < b.val := (orderedLabelRequest G c requests feasible batch label hcard).strictMono hkj
  have hl : pairLabel G c requests feasible a.val = pairLabel G c requests feasible b.val := ha.2.2.trans hb.2.2.symm
  have hx : (labelFarSequence G c hc requests feasible fallback batch label hcard (newIndex j)).val =
      farVertex G c requests feasible b hb.2.1 := rfl
  have hz : (labelFarSequence G c hc requests feasible fallback batch label hcard k).val =
      farVertex G c requests feasible a ha.2.1 := rfl
  dsimp only
  change ∃ hr : G.Reachable _ _, _ ∧ _
  rw [hx, hz]
  have hm := earlier_far_mem_selectedComponent G c requests feasible a b hab ha.1 ha.2.1 hb.2.1 hl
  refine ⟨farVertex_reachable G c requests feasible b hb.2.1 _ hm, ?_⟩
  exact earlier_far_proxy_metric G c (fun e he => le_of_lt (hc e he)) requests feasible
    a b hab ha.1 ha.2.1 hb.2.1 hl

end OnlineSteinerForest.UpperBound
