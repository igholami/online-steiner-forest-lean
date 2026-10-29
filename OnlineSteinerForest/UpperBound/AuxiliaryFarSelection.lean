import OnlineSteinerForest.UpperBound.AuxiliarySelectedComponent
import OnlineSteinerForest.UpperBound.AuxiliaryFarEndpoint

/-! Far endpoints are chosen from actual requests and satisfy helpful-pair metric conditions. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def farVertex (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (ht : (touchedAt G c requests feasible i.val).Nonempty) : V :=
  farEndpoint G c (boughtBefore G c requests feasible i.val) requests[i.val].1 requests[i.val].2
    (feasible _ (List.getElem_mem i.isLt)) (selectedComponent G c requests feasible i ht)
    (selectedComponent_input_reach G c requests feasible i ht)

theorem farVertex_reachable (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (ht : (touchedAt G c requests feasible i.val).Nonempty)
    (v : V) (hv : v ∈ selectedComponent G c requests feasible i ht) :
    G.Reachable (farVertex G c requests feasible i ht) v :=
  farEndpoint_reachable G c _ _ _ _ _ _ v hv

/-- Any earlier same-label far endpoint in the selected component gives a proxy
with half-payment separation before request `i`, and zero residual distance after. -/
theorem farVertex_proxy (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (ht : (touchedAt G c requests feasible i.val).Nonempty)
    (v : V) (hv : v ∈ selectedComponent G c requests feasible i ht) :
    payment G c requests feasible i / 2 ≤
      residualDistance G c (boughtBefore G c requests feasible i.val)
        (farVertex G c requests feasible i ht) v (farVertex_reachable G c requests feasible i ht v hv) ∧
    residualDistance G c (boughtBefore G c requests feasible (i.val + 1))
      (farVertex G c requests feasible i ht) v (farVertex_reachable G c requests feasible i ht v hv) = 0 := by
  obtain ⟨p, hp, heq⟩ := (shortestPathEdges_spec G c (boughtBefore G c requests feasible i.val)
    requests[i.val].1 requests[i.val].2 (feasible _ (List.getElem_mem i.isLt))).1
  have htouch := selectedRoot_after_connected G c requests feasible i ht
  rw [boughtBefore_succ] at htouch
  have htpath := touched_root_has_path_vertex G c _ _ _ _
    (selectedRoot G c requests feasible i ht) p heq htouch
  have hproxy := farEndpoint_proxy G c hc _ (boughtBefore_input G c requests feasible i.val)
    requests[i.val].1 requests[i.val].2 (feasible _ (List.getElem_mem i.isLt))
    (selectedComponent G c requests feasible i ht) (componentVertices_nonempty _ _)
    (selectedComponent_input_reach G c requests feasible i ht) (componentVertices_connected _ _)
    p heq htpath v hv
  rw [boughtBefore_succ]
  exact hproxy

end OnlineSteinerForest.UpperBound
