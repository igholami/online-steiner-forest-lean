import OnlineSteinerForest.UpperBound.AuxiliaryRealization
import OnlineSteinerForest.Graph.ResidualMetric

/-! A component-tree proxy metric is realized by an actual simple input-graph path. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_proxy_realizing_path (G H : SimpleGraph V) (hle : H ≤ G)
    (c : Sym2 V → ℝ) (K : H.ConnectedComponent) (u v : K) :
    ∃ P, IsPathEdges G u.val v.val P ∧
      edgeCost c P = residualDistance K.toSimpleGraph (fun e => c (Sym2.map Subtype.val e))
        ∅ u v (K.connected_toSimpleGraph.preconnected u v) := by
  obtain ⟨p, hp, heq⟩ := (shortestPathEdges_spec K.toSimpleGraph
    (fun e => c (Sym2.map Subtype.val e)) ∅ u v (K.connected_toSimpleGraph.preconnected u v)).1
  let q := (p.map K.toSimpleGraph_hom).mapLe hle
  refine ⟨q.edges.toFinset, ⟨q, ?_, rfl⟩, ?_⟩
  · exact (hp.map Subtype.val_injective).mapLe hle
  · change edgeCost c ((p.map K.toSimpleGraph_hom).mapLe hle).edges.toFinset = _
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges, SimpleGraph.Walk.edges_map]
    change edgeCost c (p.edges.map (Sym2.map Subtype.val)).toFinset = _
    have hfin : (p.edges.map (Sym2.map Subtype.val)).toFinset =
        p.edges.toFinset.image (Sym2.map Subtype.val) := by
      ext e
      simp
    rw [hfin]
    change edgeCost c (p.edges.toFinset.image (Sym2.map Subtype.val)) = _
    change _ = residualCost (fun e => c (Sym2.map Subtype.val e)) ∅
      (shortestPathEdges K.toSimpleGraph (fun e => c (Sym2.map Subtype.val e)) ∅ u v _)
    rw [residualCost_empty, ← heq]
    exact Finset.sum_image (fun _ _ _ _ h => Sym2.map.injective Subtype.val_injective h)

end OnlineSteinerForest.UpperBound
