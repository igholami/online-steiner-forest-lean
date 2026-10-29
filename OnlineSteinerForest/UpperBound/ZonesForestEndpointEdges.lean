import OnlineSteinerForest.UpperBound.SmallReferenceCost
import OnlineSteinerForest.UpperBound.ZonesSubdivisionUniformCertificate
import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary

/-! Every original vertex in a positive-cost reference component remains on an expanded component edge. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem positive_component_has_incident_edge (F : SimpleGraph V) (c : Sym2 V → ℝ) (r : V)
    (hcost : 0 < edgeCost c (componentEdges F (F.connectedComponentMk r))) :
    ∃ w, F.Adj r w ∧ s(r, w) ∈ componentEdges F (F.connectedComponentMk r) := by
  let C := F.connectedComponentMk r
  change 0 < edgeCost c (componentEdges F C) at hcost
  have hne : (componentEdges F C).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simpa [he, edgeCost] using hcost
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.inductionOn with
  | _ u v =>
    obtain ⟨huv, hu⟩ := (mem_componentEdges F C u v).mp he
    have huC := (C.mem_supp_iff u).mpr hu
    have hvC := C.mem_supp_of_adj_mem_supp huC huv
    have hrC : r ∈ C.supp := rfl
    have hz : ∃ z ∈ C.supp, r ≠ z := by
      by_cases hru : r = u
      · exact ⟨v, hvC, fun hrv => huv.ne (hru.symm.trans hrv)⟩
      · exact ⟨u, huC, hru⟩
    obtain ⟨z, hzC, hrz⟩ := hz
    obtain ⟨w, hw⟩ := (C.reachable_of_mem_supp hrC hzC).nonempty_neighborSet_left hrz
    exact ⟨w, hw, (mem_componentEdges F C r w).mpr ⟨hw, rfl⟩⟩

theorem expanded_component_covers_vertex (F : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) (r : V)
    (hcost : 0 < edgeCost c (componentEdges F (F.connectedComponentMk r))) (n : ℕ) :
    zoneSupport (subdivisionEdges (componentEdges F (F.connectedComponentMk r)) n)
      (subdivisionEmbedding V n r) := by
  obtain ⟨w, hrw, he⟩ := positive_component_has_incident_edge F c r hcost
  let E := componentEdges F (F.connectedComponentMk r)
  have hnd : ∀ e ∈ E, ¬e.IsDiag := fun e he => F.not_isDiag_of_mem_edgeSet
    (F.mem_edgeFinset.mp (componentEdges_subset F _ he))
  have hn : ∀ e ∈ E, 0 ≤ c e := fun e he => hc e (F.mem_edgeFinset.mp (componentEdges_subset F _ he))
  let cert := uniformSubdivisionCertificate E c hnd hn n
  have hadj : (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Adj r w := ⟨he, hrw.ne⟩
  obtain ⟨q, hq⟩ := cert.realize (SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil)
  have hnon : ¬q.Nil := q.not_nil_of_ne (cert.vertices.injective.ne hrw.ne)
  obtain ⟨e, heq, hre⟩ := (SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnon).mp q.start_mem_support
  have heF : e ∈ subdivisionEdges E n := by
    have heG := q.edges_subset_edgeSet heq
    have heG' : e ∈ (subdivisionEdges E n : Set (Sym2 (subdivisionVertices V n))) \ Sym2.diagSet := by
      simpa only [SimpleGraph.edgeSet_fromEdgeSet] using heG
    exact heG'.1
  have hcert : cert.vertices = subdivisionEmbedding V n := uniformSubdivisionCertificate_vertices E c hnd hn n
  exact ⟨e, heF, hcert ▸ hre⟩

end OnlineSteinerForest.UpperBound
