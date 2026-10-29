import OnlineSteinerForest.UpperBound.RetainedReplacementCore
import OnlineSteinerForest.UpperBound.RetainedForestZones
import OnlineSteinerForest.UpperBound.RetainedZoneAssignment
import OnlineSteinerForest.UpperBound.RetainedActualCaps

/-! The manuscript's retained-request estimate, derived from the actual greedy algorithm. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

theorem retained_replacement_count (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (hforest : (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).IsAcyclic)
    (time : I ↪ Fin requests.length) (out : I → AuxiliaryOutput V) (scale : ℝ)
    (hs : 0 < scale) (helpful : ∀ i, HelpfulAt G c requests feasible (time i) scale (out i))
    (hlarge : ∀ i,
      65536*(cycleFactor requests.length : ℝ)^3*scale ≤ referenceTreeCost E c (out i).left ∧
      65536*(cycleFactor requests.length : ℝ)^3*scale ≤ referenceTreeCost E c (out i).right)
    (marks : Finset V) :
    (Fintype.card I : ℝ)*scale ≤
      32*(cycleFactor requests.length : ℝ)*(edgeCost c E-edgeCost c (referenceUpdate G c hc E hE marks)) +
      2^24*(cycleFactor requests.length : ℝ)^4*marks.card*scale +
      2^28*cycleFactor (cycleFactor requests.length)*edgeCost c E := by
  let L := cycleFactor requests.length
  let M : ℝ := (zoneMultiplier L : ℝ)*scale
  have hL : 1 ≤ L := cycleFactor_pos requests.length
  have hM : 0 < M := by
    have hm := zoneMultiplier_ge L hL
    dsimp [M]
    positivity
  obtain ⟨n, cert, A, p, hsub, hprop, hsep, hcount, hcover⟩ :=
    retained_forest_zones G E hE hforest c hc M hM
  let zones : ↥p.zones → Finset (Sym2 (subdivisionVertices V (n+1))) := Subtype.val
  have hlarge' (i : I) : M ≤ referenceTreeCost E c (out i).left ∧
      M ≤ referenceTreeCost E c (out i).right := by
    simpa only [M, zoneMultiplier, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hlarge i
  let left : I → ↥p.zones := fun i => assignedZone p.zones (cert.vertices (out i).left) (hcover _ (hlarge' i).1)
  let right : I → ↥p.zones := fun i => assignedZone p.zones (cert.vertices (out i).right) (hcover _ (hlarge' i).2)
  have hl : ∀ i, zoneSupport (zones (left i)) (cert.vertices (out i).left) :=
    fun i => assignedZone_support _ _ _
  have hr : ∀ i, zoneSupport (zones (right i)) (cert.vertices (out i).right) :=
    fun i => assignedZone_support _ _ _
  have hconn : ∀ z, ZoneConnected (zones z) := fun z => (p.good z.val z.property).1
  have hnonempty : ∀ z, (zones z).Nonempty := by
    intro z
    by_contra hn
    have he : zones z = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hb := (p.good z.val z.property).2.1
    change M ≤ edgeCost _ (zones z) at hb
    rw [he, edgeCost, Finset.sum_empty] at hb
    exact (not_le_of_gt hM) hb
  have hdis : (↑(Finset.univ : Finset ↥p.zones) : Set ↥p.zones).PairwiseDisjoint zones := by
    intro a _ b _ hab
    exact p.disjoint a.val a.property b.val b.property (fun h => hab (Subtype.ext h))
  have hcaps := actual_assigned_multiplicity_caps G c hc requests feasible E hE
    (subdivisionEdges E (n+1)) (subdivisionCost c (n+1)) cert hsep
    (fun e he => (hprop e he).2) zones hconn hnonempty (fun z => hsub z.val z.property)
    time out scale helpful left right hl hr hs L hL
    (fun z => by simpa only [mul_assoc] using (p.good z.val z.property).2.2)
  exact retained_assigned_core_estimate G c hc requests feasible E hE
    (subdivisionEdges E (n+1)) (subdivisionCost c (n+1)) cert hsep
    (fun e he => (hprop e he).1) (fun e he => (hprop e he).2)
    zones left right time out scale hs helpful hl hr (fun z => hsub z.val z.property)
    hdis hconn (fun z => (p.good z.val z.property).2.1)
    (fun z => (p.good z.val z.property).2.2)
    (by simpa only [Fintype.card_coe, M, mul_assoc] using hcount)
    (fun z => hcaps.1 z (Finset.mem_univ z)) hcaps.2 marks

end OnlineSteinerForest.UpperBound
