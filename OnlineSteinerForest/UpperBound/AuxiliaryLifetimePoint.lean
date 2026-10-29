import OnlineSteinerForest.UpperBound.AuxiliaryChronology

/-! Far endpoints lie in the standard connected-component tree of their final lifetime. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def lifetimeGraph (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (label : ℕ) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible (finalLifetime G c requests feasible label) : Set (Sym2 V))

noncomputable def lifetimeComponent (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (fallback : V) (label : ℕ) : (lifetimeGraph G c requests feasible label).ConnectedComponent :=
  (lifetimeGraph G c requests feasible label).connectedComponentMk (requestSource requests fallback label)

theorem farVertex_in_lifetime (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (i : Fin requests.length) (hp : 0 < blockPayment G c requests feasible i.val)
    (ht : (touchedAt G c requests feasible i.val).Nonempty) :
    farVertex G c requests feasible i ht ∈
      (lifetimeComponent G c requests feasible fallback (pairLabel G c requests feasible i.val)).supp := by
  let C := finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)
  have hC := (finalLifetime_contains_snapshot G c requests feasible (i.val + 1) (by omega)
    (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))).1
  have hiC := request_mem_finalLifetime G c requests feasible i hp
  have hlC := scanHistory_snapshot_label_mem
    (fun j => 0 < blockPayment G c requests feasible j) (touchesBlock G c requests feasible) requests.length C hC
  have hClabel : C.label = pairLabel G c requests feasible i.val := by
    exact finalLifetime_label G c requests feasible (i.val + 1) (by omega)
      (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))
  have hlabelLen := greedyHistory_snapshot_members G c requests feasible requests.length C hC C.label hlC
  have hconn := snapshot_requests_connected G c hc requests feasible requests.length le_rfl C hC
    ⟨C.label, hlabelLen⟩ i hlC hiC
  have hfar : farVertex G c requests feasible i ht = requests[i.val].1 ∨
      farVertex G c requests feasible i ht = requests[i.val].2 := farEndpoint_eq G c _ _ _ _ _ _
  have hr : (lifetimeGraph G c requests feasible (pairLabel G c requests feasible i.val)).Reachable
      (requestSource requests fallback (pairLabel G c requests feasible i.val)) (farVertex G c requests feasible i ht) := by
    have hroot : requestSource requests fallback (pairLabel G c requests feasible i.val) = requests[C.label].1 := by
      rw [← hClabel, requestSource_eq requests fallback C.label hlabelLen]
    rw [hroot]
    rcases hfar with hfar | hfar <;> rw [hfar]
    · exact hconn.1
    · exact hconn.2
  exact SimpleGraph.ConnectedComponent.sound hr.symm

end OnlineSteinerForest.UpperBound
