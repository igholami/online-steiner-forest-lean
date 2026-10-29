import OnlineSteinerForest.UpperBound.ReplacementDomination
import OnlineSteinerForest.UpperBound.ZonesSkeletonMain

/-! Dense core graphs construct an actual cheap skeleton through dominating stars and an interstar forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem exists_dense_zone_skeleton (core : SimpleGraph V) (ambient : SimpleGraph W)
    (hdeg : ∀ v, 8191 ≤ core.degree v) (zones : V → Finset (Sym2 W))
    (c : Sym2 W → ℝ) (M : ℝ) (hM : 0 ≤ M) (hc : ∀ e ∈ ambient.edgeSet, 0 ≤ c e)
    (hinput : ∀ v, ∀ e ∈ zones v, e ∈ ambient.edgeSet)
    (hzone : ∀ v, edgeCost c (zones v) ≤ 3 * M)
    (hconn : ∀ v, ZoneConnected (zones v)) (hpoint : ∀ v, ∃ w, zoneSupport (zones v) w)
    (hreal : ∀ u v, core.Adj u v → ∃ a b : W, ∃ P : Finset (Sym2 W),
      zoneSupport (zones u) a ∧ zoneSupport (zones v) b ∧
        IsPathEdges ambient a b P ∧ edgeCost c P ≤ M / 256) :
    ∃ (S : Finset (Sym2 W)) (anchor : V → W),
      (∀ e ∈ S, e ∈ ambient.edgeSet) ∧ edgeCost c S ≤ (11 / 512 : ℝ) * M * Fintype.card V ∧
      (∀ v, zoneSupport (zones v) (anchor v)) ∧ ∀ u v, core.Reachable u v →
        (SimpleGraph.fromEdgeSet (S : Set (Sym2 W))).Reachable (anchor u) (anchor v) := by
  obtain ⟨centers, hdom, hcenters⟩ := exists_small_dominating_set core hdeg
  obtain ⟨stars⟩ := exists_star_contraction core centers hdom
  obtain ⟨forest⟩ := exists_interstar_forest stars
  exact exists_zone_skeleton forest ambient zones c M hM hc hinput hzone hconn hpoint hcenters
    (fun i => hreal _ _ (forest.link_adjacent i))

end OnlineSteinerForest.UpperBound
