import OnlineSteinerForest.UpperBound.RetainedCoreRestriction
import OnlineSteinerForest.UpperBound.ChargingZoneCore
import OnlineSteinerForest.UpperBound.ZonesDenseCandidateStructure

/-! The actual retained core's cycle rank charges its labels to exactly the removed zone edges. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W Z : Type uSelection} {I : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [DecidableEq Z]

theorem retained_core_charge (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (zones : Z → Finset (Sym2 W)) (left right : I → Z) (S : Finset Z)
    (time : I ↪ Fin requests.length) (out : I → AuxiliaryOutput V) (scale : ℝ)
    (hs : 0 < scale) (helpful : ∀ i, HelpfulAt G c requests feasible (time i) scale (out i))
    (hl : ∀ i, zoneSupport (zones (left i)) (cert.vertices (out i).left))
    (hr : ∀ i, zoneSupport (zones (right i)) (cert.vertices (out i).right))
    (hsub : ∀ z ∈ S, zones z ⊆ F) (hdis : (S : Set Z).PairwiseDisjoint zones)
    (hconn : ∀ z ∈ S, ZoneConnected (zones z)) (hne : ∀ z ∈ S, (zones z).Nonempty)
    (hdense : 2*S.card ≤ (liveEdges left right S).card) :
    ((liveEdges left right S).card : ℝ)*scale ≤
      16 * cycleFactor requests.length * edgeCost d (zoneCoreEdges (fun z : ↥S => zones z.val)) := by
  have hdisjoint : (↑(Finset.univ : Finset ↥S) : Set ↥S).PairwiseDisjoint (fun z => zones z.val) := by
    intro a _ b _ hab
    exact hdis a.property b.property (fun h => hab (Subtype.ext h))
  have hh := actual_zone_dense_charge G c hc requests feasible E hE F d cert hsep hd
    (fun z : ↥S => zones z.val) (fun z => hconn z.val z.property)
    (fun z => hne z.val z.property) (fun z => hsub z.val z.property)
    (coreTime left right S time) (fun i : ↥(liveEdges left right S) => out i.val) scale
    (fun i => helpful i.val) (coreLeft left right S) (coreRight left right S)
    (fun i => hl i.val) (fun i => hr i.val) hs
    (by simpa only [Fintype.card_coe] using hdense) hdisjoint
  simpa only [Fintype.card_coe, zoneCoreEdges] using hh

end OnlineSteinerForest.UpperBound
