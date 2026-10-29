import OnlineSteinerForest.UpperBound.ChargingActualCore
import OnlineSteinerForest.UpperBound.ZoneCopiesChosen
import OnlineSteinerForest.UpperBound.ZonesCost

/-! Actual helpful paths have bounded multiplicity across at most two connected zones. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]
open scoped Classical
variable {V W Z : Type uSelection} {J : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype Z] [DecidableEq Z] [Fintype J] [DecidableEq J]
variable (G : SimpleGraph V) (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e)
  (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
  (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, e ∈ G.edgeSet)
  (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) (cert : ZoneSubdivisionCertificate E c F d)
  (hsep : ∀ e : Sym2 V, Sym2.map cert.vertices e ∉ F) (hd : ∀ e ∈ F, 0 ≤ d e)
  (zones : Z → Finset (Sym2 W)) (hconn : ∀ z, ZoneConnected (zones z))
  (hne : ∀ z, (zones z).Nonempty) (hsub : ∀ z, zones z ⊆ F)
  (time : J ↪ Fin requests.length) (out : J → AuxiliaryOutput V) (scale : ℝ)
  (helpful : ∀ j, HelpfulAt G c requests feasible (time j) scale (out j))
  (zl zr : J → Z)
  (hl : ∀ j, zoneSupport (zones (zl j)) (cert.vertices (out j).left))
  (hr : ∀ j, zoneSupport (zones (zr j)) (cert.vertices (out j).right))
include hc hE hsep hd hconn hne hsub helpful hl hr

theorem actual_zone_dense_charge (hs : 0 < scale)
    (hdense : 2 * Fintype.card Z ≤ Fintype.card J)
    (hdisjoint : ((Finset.univ : Finset Z) : Set Z).PairwiseDisjoint zones) :
    (Fintype.card J : ℝ) * scale ≤ 16 * cycleFactor requests.length *
      edgeCost d (Finset.univ.biUnion zones) := by
  let T := chosenZoneTrees zones hconn hne
  have hT := chosenZoneTrees_le zones hconn hne
  have ht := chosenZoneTrees_tree zones hconn hne
  let left : J → Σ z, ZoneSupportVertex (zones z) := fun j => ⟨zl j, cert.vertices (out j).left, hl j⟩
  let right : J → Σ z, ZoneSupportVertex (zones z) := fun j => ⟨zr j, cert.vertices (out j).right, hr j⟩
  have hcharge := actual_copied_dense_charge G c hc requests feasible E hE F d cert hsep hd
    (zoneCopyProjection zones) (zoneCopyGraph T) (zoneCopyGraph_acyclic T (fun z => (ht z).2))
    (fun u v h => ⟨(zoneCopyGraph_project_edge zones T hT h).1,
      hsub u.1 (zoneCopyGraph_project_edge zones T hT h).2⟩)
    left right time out scale helpful (fun _ => rfl) (fun _ => rfl) hs
    (by simpa only [zoneCopy_component_count T (fun z => (ht z).1), Nat.card_eq_fintype_card] using hdense)
  have hcost := zoneCopies_clipped_cost_le_sum zones T hT d (fun z e he => hd e (hsub z he))
  have hsum := zone_cost_sum d Finset.univ zones hdisjoint
  rw [hsum] at hcost
  exact hcharge.trans (mul_le_mul_of_nonneg_left hcost (by positivity))

end OnlineSteinerForest.UpperBound
