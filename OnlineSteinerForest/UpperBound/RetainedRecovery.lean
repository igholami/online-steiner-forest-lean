import OnlineSteinerForest.UpperBound.ZonesSubdivisionRecovery
import OnlineSteinerForest.UpperBound.ReferenceCandidate

/-! Recover a concrete subdivided dense candidate before comparing the actual original-edge update. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical

variable {V W : Type uSelection} [Fintype V] [DecidableEq V] [DecidableEq W]

theorem retained_recovery_saving (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ)
    (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (marks : Finset V) (candidate : Finset (Sym2 W))
    (hinput : ∀ e ∈ candidate, e ∈ (mixedSubdivisionGraph G cert.vertices F).edgeSet)
    (M coreCost : ℝ)
    (hcost : edgeCost (mixedSubdivisionCost cert.vertices F d c) candidate ≤
      edgeCost (mixedSubdivisionCost cert.vertices F d c) F - coreCost / 2 +
        8 * M * (marks.image cert.vertices).card)
    (hpreserve : ∀ u ∈ marks.image cert.vertices, ∀ v ∈ marks.image cert.vertices,
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 W))).Reachable u v →
      (SimpleGraph.fromEdgeSet (candidate : Set (Sym2 W))).Reachable u v) :
    coreCost / 2 - 8 * M * marks.card ≤
      edgeCost c E - edgeCost c (referenceUpdate G c hc E hE marks) := by
  obtain ⟨P, hP, hcostP, hrecover⟩ := recover_mixed_candidate G c hc E hE F d cert hsep candidate hinput
  have hmarked : ∀ u ∈ marks, ∀ v ∈ marks,
      (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Reachable u v →
      (SimpleGraph.fromEdgeSet (P : Set (Sym2 V))).Reachable u v := by
    intro u hu v hv huv
    obtain ⟨p⟩ := huv
    obtain ⟨q, _⟩ := cert.realize p
    exact hrecover u v (hpreserve (cert.vertices u) (Finset.mem_image_of_mem _ hu)
      (cert.vertices v) (Finset.mem_image_of_mem _ hv) ⟨q⟩)
  have hupdate := referenceUpdate_cost_le_candidate G c hc E hE marks P hP hmarked
  have hbase : edgeCost (mixedSubdivisionCost cert.vertices F d c) F = edgeCost c E :=
    (mixedSubdivisionCost_reference_cost cert.vertices F d c F (Finset.Subset.refl F)).trans cert.cost_eq
  have hcard : (marks.image cert.vertices).card = marks.card :=
    Finset.card_image_of_injective marks cert.vertices.injective
  rw [hbase, hcard] at hcost
  linarith

end OnlineSteinerForest.UpperBound
