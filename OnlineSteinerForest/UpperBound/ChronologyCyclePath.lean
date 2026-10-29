import OnlineSteinerForest.UpperBound.GirthCycleSupport
import OnlineSteinerForest.UpperBound.GirthResidualDistance
import Mathlib.Data.List.Perm.Subperm

/-! Deleting any edge of a standard cycle leaves a simple path within its support. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} {G : SimpleGraph V}

theorem cycle_avoiding_edge_path {z u v : V} (c : G.Walk z z) (hc : c.IsCycle)
    (he : s(u, v) ∈ c.edges) :
    ∃ p : G.Walk u v, p.IsPath ∧ ∀ e ∈ p.edges, e ∈ c.edges ∧ e ≠ s(u, v) := by
  classical
  let H := SimpleGraph.fromEdgeSet c.edgeSet
  have hHG : H ≤ G := by
    apply (SimpleGraph.fromEdgeSet_le G).mpr
    intro e he
    exact c.edges_subset_edgeSet he.1
  have hCH : ∀ e ∈ c.edges, e ∈ H.edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨he, G.not_isDiag_of_mem_edgeSet (c.edges_subset_edgeSet he)⟩
  let C := c.transfer H hCH
  have hC : C.IsCycle := hc.transfer _
  have hselected : s(u, v) ∈ C.edges := by simpa [C] using he
  have hreach : (H.deleteEdges {s(u, v)}).Reachable u v :=
    ((H.adj_and_reachable_delete_edges_iff_exists_cycle).mpr ⟨z, C, hC, hselected⟩).2
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hle : H.deleteEdges {s(u, v)} ≤ G := (SimpleGraph.deleteEdges_le _).trans hHG
  refine ⟨p.mapLe hle, hp.mapLe hle, ?_⟩
  intro e he
  have hm := p.edges_subset_edgeSet (by simpa using he)
  rw [SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_fromEdgeSet] at hm
  exact ⟨hm.1.1, by simpa using hm.2⟩

theorem ennreal_sum_map_le_of_sublist {A : Type*} (w : A → ENNReal)
    {ds es : List A} (h : ds.Sublist es) : (ds.map w).sum ≤ (es.map w).sum := by
  induction h with
  | slnil => simp
  | cons a h ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ih.trans (le_add_of_nonneg_left (by exact bot_le))
  | cons_cons a h ih => simpa only [List.map_cons, List.sum_cons] using add_le_add le_rfl ih

theorem ennreal_nodup_sum_map_le_of_subset {A : Type*} (w : A → ENNReal)
    {ds es : List A} (hd : ds.Nodup) (hsub : ds ⊆ es) : (ds.map w).sum ≤ (es.map w).sum := by
  obtain ⟨xs, hperm, hsl⟩ := hd.subperm hsub
  rw [← (hperm.map w).sum_eq]
  exact ennreal_sum_map_le_of_sublist w hsl

end OnlineSteinerForest.UpperBound
