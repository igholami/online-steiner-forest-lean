import OnlineSteinerForest.UpperBound.AuxiliaryFarSelection
import OnlineSteinerForest.UpperBound.HistoryChronology
import OnlineSteinerForest.UpperBound.HistoryPrefixConnected

/-! Earlier far endpoints with the same persistent label lie in the selected old component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem earlier_far_mem_selectedComponent (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i j : Fin requests.length) (hij : i.val < j.val)
    (hpi : 0 < blockPayment G c requests feasible i.val)
    (hti : (touchedAt G c requests feasible i.val).Nonempty)
    (htj : (touchedAt G c requests feasible j.val).Nonempty)
    (hl : pairLabel G c requests feasible i.val = pairLabel G c requests feasible j.val) :
    farVertex G c requests feasible i hti ∈ selectedComponent G c requests feasible j htj := by
  let D := MergeHistory.chosen (touchedAt G c requests feasible j.val) htj
  have hD := selectedOld_active G c requests feasible j.val htj
  have hDl := selectedOld_label G c requests feasible j.val htj
  have hCi := requestCluster_active G c requests feasible i.val hpi
  have hs := earlier_same_label_members G c requests feasible (i.val + 1) j.val (by omega)
    (requestCluster G c requests feasible i.val) D (Or.inl hCi) (Or.inl hD) (hl.trans hDl.symm)
  have hiD : i.val ∈ D.members := hs (MergeHistory.new_mem_merged _ _)
  have hlabel := (greedyHistory_invariant G c requests feasible j.val).partition.label_mem D hD
  have hconn := greedyHistory_members_connected G c requests feasible requests[j.val].1 j.val D hD
    D.label hlabel i.val hiD
  rw [requestSource_eq requests requests[j.val].1 i.val i.isLt] at hconn
  have htarget := hconn.trans (request_reachable_after G c requests feasible i j.val hij)
  have hfar : farVertex G c requests feasible i hti = requests[i.val].1 ∨
      farVertex G c requests feasible i hti = requests[i.val].2 :=
    farEndpoint_eq G c _ _ _ _ _ _
  apply (mem_componentVertices _ _ _).mpr
  rcases hfar with hfar | hfar
  · rw [hfar]
    exact hconn
  · rw [hfar]
    exact htarget

/-- Exact chronological metric condition for a proxy to any earlier same-label far endpoint. -/
theorem earlier_far_proxy_metric (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i j : Fin requests.length) (hij : i.val < j.val)
    (hpi : 0 < blockPayment G c requests feasible i.val)
    (hti : (touchedAt G c requests feasible i.val).Nonempty)
    (htj : (touchedAt G c requests feasible j.val).Nonempty)
    (hl : pairLabel G c requests feasible i.val = pairLabel G c requests feasible j.val) :
    let hmem := earlier_far_mem_selectedComponent G c requests feasible i j hij hpi hti htj hl
    let hr := farVertex_reachable G c requests feasible j htj (farVertex G c requests feasible i hti) hmem
    payment G c requests feasible j / 2 ≤
      residualDistance G c (boughtBefore G c requests feasible j.val)
        (farVertex G c requests feasible j htj) (farVertex G c requests feasible i hti) hr ∧
    residualDistance G c (boughtBefore G c requests feasible (j.val + 1))
      (farVertex G c requests feasible j htj) (farVertex G c requests feasible i hti) hr = 0 := by
  exact farVertex_proxy G c hc requests feasible j htj _
    (earlier_far_mem_selectedComponent G c requests feasible i j hij hpi hti htj hl)

end OnlineSteinerForest.UpperBound
