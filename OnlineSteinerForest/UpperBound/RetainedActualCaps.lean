import OnlineSteinerForest.UpperBound.RetainedPairRestriction
import OnlineSteinerForest.UpperBound.ChargingZoneCap

/-! Actual greedy helpful endpoints supply all loop and parallel caps for the computed zone graph. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical

variable {V W Z : Type uSelection} {I : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]

theorem actual_assigned_multiplicity_caps (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
    (zones : Z → Finset (Sym2 W)) (hconn : ∀ z, ZoneConnected (zones z))
    (hne : ∀ z, (zones z).Nonempty) (hsub : ∀ z, zones z ⊆ F)
    (time : I ↪ Fin requests.length) (out : I → AuxiliaryOutput V) (scale : ℝ)
    (helpful : ∀ i, HelpfulAt G c requests feasible (time i) scale (out i))
    (left right : I → Z)
    (hl : ∀ i, zoneSupport (zones (left i)) (cert.vertices (out i).left))
    (hr : ∀ i, zoneSupport (zones (right i)) (cert.vertices (out i).right))
    (hs : 0 < scale) (L : ℕ) (hL : 1 ≤ L)
    (hupper : ∀ z, edgeCost d (zones z) ≤ 3 * zoneMultiplier L * scale) :
    (∀ z ∈ (Finset.univ : Finset Z), (loopsAt left right z).card ≤ parallelCap L) ∧
      ∀ u v, (parallelEdges left right Finset.univ u v).card ≤ parallelCap L := by
  apply loops_parallel_caps_of_two_zone_caps left right Finset.univ (parallelCap L)
  intro A _ hA T hleft hright
  let leftT : ↥T → ↥A := fun i => ⟨left i.val, hleft i.val i.property⟩
  let rightT : ↥T → ↥A := fun i => ⟨right i.val, hright i.val i.property⟩
  have h := actual_zone_multiplicity_cap G c hc requests feasible E hE F d cert hsep hd
    (fun z : ↥A => zones z.val) (fun z => hconn z.val) (fun z => hne z.val) (fun z => hsub z.val)
    (restrictedAuxiliaryTime time T) (fun i : ↥T => out i.val) scale (fun i => helpful i.val)
    leftT rightT (fun i => hl i.val) (fun i => hr i.val) hs
    (by simpa only [Fintype.card_coe] using hA) L hL (fun z => hupper z.val)
  simpa only [Fintype.card_coe] using h

end OnlineSteinerForest.UpperBound
