import OnlineSteinerForest.UpperBound.ZonesDenseSkeleton
import OnlineSteinerForest.UpperBound.ZonesMarkedAttachments
import OnlineSteinerForest.Graph.ResidualBounds

/-! Construct the actual union of kept edges, dense skeleton, and marked attachments. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem exists_dense_candidate_raw (core : SimpleGraph V) (ambient old : SimpleGraph W)
    (hdeg : ∀ v, 8191 ≤ core.degree v) (zones : V → Finset (Sym2 W))
    (kept : Finset (Sym2 W)) (marks : Finset W) (c : Sym2 W → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hc : ∀ e ∈ ambient.edgeSet, 0 ≤ c e)
    (hkept : ∀ e ∈ kept, e ∈ ambient.edgeSet) (hinput : ∀ v, ∀ e ∈ zones v, e ∈ ambient.edgeSet)
    (hzone : ∀ v, edgeCost c (zones v) ≤ 3 * M)
    (hconn : ∀ v, ZoneConnected (zones v)) (hpoint : ∀ v, ∃ w, zoneSupport (zones v) w)
    (hreal : ∀ u v, core.Adj u v → ∃ a b : W, ∃ P : Finset (Sym2 W),
      zoneSupport (zones u) a ∧ zoneSupport (zones v) b ∧
        IsPathEdges ambient a b P ∧ edgeCost c P ≤ M / 256)
    (hcover : ∀ u v, old.Adj u v → s(u, v) ∈ kept ∨
      ∃ i, zoneSupport (zones i) u ∧ zoneSupport (zones i) v) :
    ∃ C : Finset (Sym2 W), (∀ e ∈ C, e ∈ ambient.edgeSet) ∧
      edgeCost c C ≤ edgeCost c kept + (11 / 512 : ℝ) * M * Fintype.card V +
        6 * M * ((Nat.card core.ConnectedComponent : ℝ) + marks.card) ∧
      ∀ u ∈ marks, ∀ v ∈ marks, old.Reachable u v →
        (SimpleGraph.fromEdgeSet (C : Set (Sym2 W))).Reachable u v := by
  classical
  letI : Fintype core.ConnectedComponent := Fintype.ofFinite _
  obtain ⟨S, anchor, hS, hScost, hanchor, hlink⟩ := exists_dense_zone_skeleton core ambient hdeg
    zones c M hM hc hinput hzone hconn hpoint hreal
  let pick : (C : core.ConnectedComponent) → C := fun C => Classical.choice C.connected_toSimpleGraph.nonempty
  let root : core.ConnectedComponent → W := fun C => anchor (pick C).val
  have hroot : ∀ v, (SimpleGraph.fromEdgeSet (S : Set (Sym2 W))).Reachable
      (anchor v) (root (core.connectedComponentMk v)) := by
    intro v
    apply hlink
    apply SimpleGraph.ConnectedComponent.exact
    exact (pick (core.connectedComponentMk v)).property.symm
  have hzoneReach : ∀ i v, zoneSupport (zones i) v →
      (SimpleGraph.fromEdgeSet (zones i : Set (Sym2 W))).Reachable v (anchor i) := by
    intro i v hv
    obtain ⟨e, he, hmem⟩ := hanchor i
    exact (hconn i).root_at hv e he (anchor i) hmem
  obtain ⟨A, hA, hAcost, hmarks⟩ := exists_marked_attachments ambient old c hc kept S zones
    (fun i => {v | zoneSupport (zones i) v}) core.connectedComponentMk anchor root marks (3 * M)
    (by positivity) hinput hzoneReach hzone hroot hcover
  have hA' : edgeCost c A ≤ 6 * M * ((Nat.card core.ConnectedComponent : ℝ) + marks.card) := by
    apply hAcost.trans_eq
    rw [Nat.card_eq_fintype_card]
    ring
  have hKS : edgeCost c (kept ∪ S) ≤ edgeCost c kept + edgeCost c S := by
    simpa only [residualCost_empty] using residualCost_union_le c ∅ kept S (fun e he => hc e (hS e he))
  have hKSA : edgeCost c (kept ∪ S ∪ A) ≤ edgeCost c (kept ∪ S) + edgeCost c A := by
    simpa only [residualCost_empty] using residualCost_union_le c ∅ (kept ∪ S) A (fun e he => hc e (hA e he))
  refine ⟨kept ∪ S ∪ A, ?_, by linarith, hmarks⟩
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · rcases Finset.mem_union.mp he with he | he
    · exact hkept e he
    · exact hS e he
  · exact hA e he

end OnlineSteinerForest.UpperBound
