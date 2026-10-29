import OnlineSteinerForest.UpperBound.HistoryPathComponents

/-! Finite vertex sets of ordinary connected components in the purchased graph. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def componentVertices (B : Finset (Sym2 V)) (root : V) : Finset V :=
  Finset.univ.filter (fun v => (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable root v)

@[simp] theorem mem_componentVertices (B : Finset (Sym2 V)) (root v : V) :
    v ∈ componentVertices B root ↔ (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable root v := by
  simp [componentVertices]

theorem componentVertices_nonempty (B : Finset (Sym2 V)) (root : V) :
    (componentVertices B root).Nonempty := ⟨root, (mem_componentVertices B root root).mpr (.refl _)⟩

theorem componentVertices_connected (B : Finset (Sym2 V)) (root : V) :
    ∀ u ∈ componentVertices B root, ∀ v ∈ componentVertices B root,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v := by
  intro u hu v hv
  exact ((mem_componentVertices B root u).mp hu).symm.trans ((mem_componentVertices B root v).mp hv)

theorem bought_reachable_input (G : SimpleGraph V) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) {u v : V}
    (h : (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v) : G.Reachable u v := by
  apply SimpleGraph.Reachable.mono _ h
  apply (SimpleGraph.fromEdgeSet_le G).mpr
  intro e he
  exact hB e he.1

theorem touched_root_has_path_vertex (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (hst : G.Reachable s t) (root : V)
    (p : G.Walk s t) (heq : p.edges.toFinset = shortestPathEdges G c B s t hst)
    (htouch : (SimpleGraph.fromEdgeSet (greedyStep G c B s t hst : Set (Sym2 V))).Reachable s root) :
    ∃ w ∈ componentVertices B root, w ∈ p.support := by
  have h : (SimpleGraph.fromEdgeSet ((B ∪ p.edges.toFinset : Finset _) : Set (Sym2 V))).Reachable root s := by
    rw [heq]
    exact htouch.symm
  obtain ⟨w, hwp, hw⟩ := (reachable_union_source_iff_touches B p).mp h
  exact ⟨w, (mem_componentVertices B root w).mpr hw, hwp⟩

end OnlineSteinerForest.UpperBound
