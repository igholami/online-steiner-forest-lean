import OnlineSteinerForest.UpperBound.RetainedHelpfulRealization
import OnlineSteinerForest.UpperBound.RetainedRecovery
import OnlineSteinerForest.UpperBound.ZonesDenseSaving

/-! Actual helpful paths construct and recover the dense-core replacement in the original graph. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W Z : Type uSelection} {I : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [DecidableEq Z]

theorem retained_dense_saving (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (hnd : ∀ e ∈ F, ¬ e.IsDiag) (hd : ∀ e ∈ F, 0 ≤ d e)
    (zones : Z → Finset (Sym2 W)) (left right : I → Z) (S : Finset Z)
    (time : I → Fin requests.length) (out : I → AuxiliaryOutput V) (scale : ℝ)
    (hs : 0 < scale) (helpful : ∀ i, HelpfulAt G c requests feasible (time i) scale (out i))
    (hl : ∀ i, zoneSupport (zones (left i)) (cert.vertices (out i).left))
    (hr : ∀ i, zoneSupport (zones (right i)) (cert.vertices (out i).right))
    (hdeg : ∀ z : ↥S, 8191 ≤ (zoneNeighborGraph left right S).degree z)
    (hsub : ∀ z ∈ S, zones z ⊆ F)
    (hdis : (S : Set Z).PairwiseDisjoint zones)
    (hlower : ∀ z ∈ S, (zoneMultiplier (cycleFactor requests.length) : ℝ) * scale ≤ edgeCost d (zones z))
    (hupper : ∀ z ∈ S, edgeCost d (zones z) ≤ 3 * ((zoneMultiplier (cycleFactor requests.length) : ℝ) * scale))
    (hconn : ∀ z ∈ S, ZoneConnected (zones z)) (marks : Finset V) :
    edgeCost d (zoneCoreEdges (fun z : ↥S => zones z.val)) / 2 -
      8 * ((zoneMultiplier (cycleFactor requests.length) : ℝ) * scale) * marks.card ≤
        edgeCost c E - edgeCost c (referenceUpdate G c hc E hE marks) := by
  let M : ℝ := (zoneMultiplier (cycleFactor requests.length) : ℝ) * scale
  let dc := mixedSubdivisionCost cert.vertices F d c
  have hM : 0 < M := by
    have hz := zoneMultiplier_ge (cycleFactor requests.length) (cycleFactor_pos requests.length)
    dsimp [M]
    positivity
  have hcost (z : ↥S) : edgeCost dc (zones z.val) = edgeCost d (zones z.val) :=
    mixedSubdivisionCost_reference_cost cert.vertices F d c _ (hsub z.val z.property)
  have hinput : ∀ e ∈ F, e ∈ (mixedSubdivisionGraph G cert.vertices F).edgeSet := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      apply (SimpleGraph.mem_edgeSet _).mpr
      exact ⟨Finset.mem_union_left _ he, fun hab => hnd _ he (by simpa [hab])⟩
  have hdj : (↑(Finset.univ : Finset ↥S) : Set ↥S).PairwiseDisjoint (fun z => zones z.val) := by
    intro a _ b _ hab
    exact hdis a.property b.property (fun h => hab (Subtype.ext h))
  obtain ⟨C, hC, hcostC, hmarks⟩ := exists_dense_replacement_candidate
    (zoneNeighborGraph left right S) (mixedSubdivisionGraph G cert.vertices F) hdeg
    (fun z : ↥S => zones z.val) F (marks.image cert.vertices) dc M hM
    (mixedSubdivisionGraph_nonneg G cert.vertices F d c hsep hd hc) hinput
    (fun z => hsub z.val z.property) hdj
    (fun z => by rw [hcost]; exact hlower z.val z.property)
    (fun z => by rw [hcost]; exact hupper z.val z.property)
    (fun z => hconn z.val z.property)
    (helpful_core_realization G c requests feasible cert.vertices F d hsep zones left right S time out scale helpful hl hr)
  have hcore : edgeCost dc (zoneCoreEdges (fun z : ↥S => zones z.val)) =
      edgeCost d (zoneCoreEdges (fun z : ↥S => zones z.val)) :=
    mixedSubdivisionCost_reference_cost cert.vertices F d c _
      (zoneCoreEdges_subset _ F (fun z => hsub z.val z.property))
  rw [hcore] at hcostC
  exact retained_recovery_saving G c hc E hE F d cert hsep marks C hC M _ hcostC hmarks

end OnlineSteinerForest.UpperBound
