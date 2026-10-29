import OnlineSteinerForest.UpperBound.ZonesSkeletonRouting
import OnlineSteinerForest.UpperBound.ZonesSkeletonCost

/-! Construct the cheap actual skeleton and one reachable anchor in every core zone. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {G : SimpleGraph V} {centers : Finset V} {stars : StarContraction G centers}

/-- Realizing the selected auxiliary links and retaining the specified zones
constructs the manuscript's cheap skeleton with all core-component connections. -/
theorem exists_zone_skeleton (f : InterstarForest stars) (ambient : SimpleGraph W)
    (zones : V → Finset (Sym2 W)) (c : Sym2 W → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ e ∈ ambient.edgeSet, 0 ≤ c e)
    (hinput : ∀ v, ∀ e ∈ zones v, e ∈ ambient.edgeSet)
    (hzone : ∀ v, edgeCost c (zones v) ≤ 3 * M)
    (hconn : ∀ v, ZoneConnected (zones v)) (hpoint : ∀ v, ∃ w, zoneSupport (zones v) w)
    (hcenters : (centers.card : ℝ) ≤ (Fintype.card V : ℝ) / 512)
    (hreal : ∀ i : f.Link, ∃ a b : W, ∃ P : Finset (Sym2 W),
      zoneSupport (zones (f.linkLeft i)) a ∧ zoneSupport (zones (f.linkRight i)) b ∧
        IsPathEdges ambient a b P ∧ edgeCost c P ≤ M / 256) :
    ∃ (S : Finset (Sym2 W)) (anchor : V → W),
      (∀ e ∈ S, e ∈ ambient.edgeSet) ∧ edgeCost c S ≤ (11 / 512 : ℝ) * M * Fintype.card V ∧
      (∀ v, zoneSupport (zones v) (anchor v)) ∧ ∀ u v, G.Reachable u v →
        (SimpleGraph.fromEdgeSet (S : Set (Sym2 W))).Reachable (anchor u) (anchor v) := by
  choose left right paths hleft hright hpaths hcost using hreal
  let d : ZoneSkeletonData f ambient zones := ⟨left, right, paths, hleft, hright, hpaths⟩
  let a : ↥centers → W := fun v => Classical.choose (hpoint v.val)
  have ha : ∀ v : ↥centers, zoneSupport (zones v.val) (a v) :=
    fun v => Classical.choose_spec (hpoint v.val)
  refine ⟨d.edges, d.anchor a, d.input_edges hinput,
    d.cost_le c M hM hc hinput hzone hcost hcenters, d.anchor_mem a ha, ?_⟩
  intro u v huv
  exact d.anchors_connected a ha hconn huv

end OnlineSteinerForest.UpperBound
