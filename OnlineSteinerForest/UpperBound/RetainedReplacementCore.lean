import OnlineSteinerForest.UpperBound.RetainedCoreCharge
import OnlineSteinerForest.UpperBound.RetainedDenseSaving
import OnlineSteinerForest.UpperBound.ZonesReplacementNumerical

/-! Sparse peeling and the recovered dense candidate give the exact retained-label budget. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W Z : Type uSelection} {I : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype Z] [DecidableEq Z] [Fintype I] [DecidableEq I]

theorem retained_assigned_core_estimate (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
    (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F)
    (hnd : ∀ e ∈ F, ¬e.IsDiag) (hd : ∀ e ∈ F, 0 ≤ d e)
    (zones : Z → Finset (Sym2 W)) (left right : I → Z)
    (time : I ↪ Fin requests.length) (out : I → AuxiliaryOutput V) (scale : ℝ)
    (hs : 0 < scale) (helpful : ∀ i, HelpfulAt G c requests feasible (time i) scale (out i))
    (hl : ∀ i, zoneSupport (zones (left i)) (cert.vertices (out i).left))
    (hr : ∀ i, zoneSupport (zones (right i)) (cert.vertices (out i).right))
    (hsub : ∀ z, zones z ⊆ F)
    (hdis : (↑(Finset.univ : Finset Z) : Set Z).PairwiseDisjoint zones)
    (hconn : ∀ z, ZoneConnected (zones z))
    (hlower : ∀ z, (zoneMultiplier (cycleFactor requests.length) : ℝ)*scale ≤ edgeCost d (zones z))
    (hupper : ∀ z, edgeCost d (zones z) ≤ 3*((zoneMultiplier (cycleFactor requests.length) : ℝ)*scale))
    (hcount : (Fintype.card Z : ℝ)*zoneMultiplier (cycleFactor requests.length)*scale ≤ edgeCost c E)
    (hloops : ∀ z, (loopsAt left right z).card ≤ parallelCap (cycleFactor requests.length))
    (hparallel : ∀ u v, (parallelEdges left right Finset.univ u v).card ≤ parallelCap (cycleFactor requests.length))
    (marks : Finset V) :
    (Fintype.card I : ℝ)*scale ≤
      32*(cycleFactor requests.length : ℝ)*(edgeCost c E - edgeCost c (referenceUpdate G c hc E hE marks)) +
      2^24*(cycleFactor requests.length : ℝ)^4*marks.card*scale +
      2^28*cycleFactor (cycleFactor requests.length)*edgeCost c E := by
  let L := cycleFactor requests.length
  let K := sparseCore left right (coreDegree L) Finset.univ
  have hL : 1 ≤ L := cycleFactor_pos requests.length
  have hKs : K ⊆ Finset.univ := (sparseCore_spec left right (coreDegree L) Finset.univ).1
  have hdeg := configured_core_minimum_degree L hL left right Finset.univ hparallel
  have hdensity := retained_core_density L hL left right Finset.univ
  have hnonempty : ∀ z, (zones z).Nonempty := by
    intro z
    by_contra hn
    have hz : zones z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hb := hlower z
    rw [hz, edgeCost, Finset.sum_empty] at hb
    have hm := zoneMultiplier_ge L hL
    change (zoneMultiplier L : ℝ)*scale ≤ 0 at hb
    nlinarith
  have hccharge := retained_core_charge G c hc requests feasible E hE F d cert hsep hd
    zones left right K time out scale hs helpful hl hr
    (fun z _ => hsub z) (fun a ha b hb hab => hdis (hKs ha) (hKs hb) hab)
    (fun z _ => hconn z) (fun z _ => hnonempty z) hdensity
  have hsaving := retained_dense_saving G c hc requests feasible E hE F d cert hsep hnd hd
    zones left right K time out scale hs helpful hl hr hdeg
    (fun z _ => hsub z) (fun a ha b hb hab => hdis (hKs ha) (hKs hb) hab)
    (fun z _ => hlower z) (fun z _ => hupper z) (fun z _ => hconn z) marks
  have hdiscard := configured_discarded_count_scale_le L hL left right Finset.univ
    (fun _ => Finset.mem_univ _) (fun _ => Finset.mem_univ _) (fun z _ => hloops z)
    scale (edgeCost c E) hs.le (by simpa only [Finset.card_univ] using hcount)
  have hcard : (liveEdges left right K).card ≤ Fintype.card I :=
    (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Finset.card_univ)
  rw [Nat.cast_sub hcard] at hdiscard
  have hsave : edgeCost d (zoneCoreEdges (fun z : ↥K => zones z.val))/2 -
      2^19*(L : ℝ)^3*marks.card*scale ≤
      edgeCost c E-edgeCost c (referenceUpdate G c hc E hE marks) := by
    convert hsaving using 1 <;> push_cast [zoneMultiplier] <;> ring
  exact replacement_count_budget (L : ℝ) (cycleFactor L) (Fintype.card I)
    (liveEdges left right K).card (edgeCost c E)
    (edgeCost c E-edgeCost c (referenceUpdate G c hc E hE marks))
    (edgeCost d (zoneCoreEdges (fun z : ↥K => zones z.val))) marks.card scale
    (by positivity) hdiscard hccharge hsave

end OnlineSteinerForest.UpperBound
