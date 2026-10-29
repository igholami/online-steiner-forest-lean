import OnlineSteinerForest.UpperBound.ZonesDenseCandidateRaw
import OnlineSteinerForest.UpperBound.ZonesDenseCandidateStructure
import OnlineSteinerForest.UpperBound.ZonesDenseComponents
import OnlineSteinerForest.UpperBound.ZonesDenseSavingNumerical

/-! Actual dense-zone replacement preserves marks and saves half the removed core cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem exists_dense_replacement_candidate (core : SimpleGraph V) (ambient : SimpleGraph W)
    (hdeg : ∀ v, 8191 ≤ core.degree v) (zones : V → Finset (Sym2 W)) (old : Finset (Sym2 W))
    (marks : Finset W) (c : Sym2 W → ℝ) (M : ℝ) (hM : 0 < M)
    (hc : ∀ e ∈ ambient.edgeSet, 0 ≤ c e) (hold : ∀ e ∈ old, e ∈ ambient.edgeSet)
    (hsub : ∀ v, zones v ⊆ old) (hdis : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint zones)
    (hlower : ∀ v, M ≤ edgeCost c (zones v)) (hupper : ∀ v, edgeCost c (zones v) ≤ 3 * M)
    (hconn : ∀ v, ZoneConnected (zones v))
    (hreal : ∀ u v, core.Adj u v → ∃ a b : W, ∃ P : Finset (Sym2 W),
      zoneSupport (zones u) a ∧ zoneSupport (zones v) b ∧
        IsPathEdges ambient a b P ∧ edgeCost c P ≤ M / 256) :
    ∃ C : Finset (Sym2 W), (∀ e ∈ C, e ∈ ambient.edgeSet) ∧
      edgeCost c C ≤ edgeCost c old - edgeCost c (zoneCoreEdges zones) / 2 + 8 * M * marks.card ∧
      ∀ u ∈ marks, ∀ v ∈ marks,
        (SimpleGraph.fromEdgeSet (old : Set (Sym2 W))).Reachable u v →
          (SimpleGraph.fromEdgeSet (C : Set (Sym2 W))).Reachable u v := by
  have hinput : ∀ v, ∀ e ∈ zones v, e ∈ ambient.edgeSet := fun v e he => hold e (hsub v he)
  have hkept : ∀ e ∈ old \ zoneCoreEdges zones, e ∈ ambient.edgeSet :=
    fun e he => hold e (Finset.mem_sdiff.mp he).1
  obtain ⟨C, hC, hcost, hmarks⟩ := exists_dense_candidate_raw core ambient
    (SimpleGraph.fromEdgeSet (old : Set (Sym2 W))) hdeg zones (old \ zoneCoreEdges zones) marks c M
    hM.le hc hkept hinput hupper hconn (zone_point_of_positive_cost zones c M hM hlower) hreal
    (old_covered_by_kept_zones zones old)
  have hcomponent : 8192 * (Nat.card core.ConnectedComponent : ℝ) ≤ Fintype.card V := by
    letI : Fintype core.ConnectedComponent := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast dense_component_count core hdeg
  have hcore := zoneCoreEdges_cost_lower zones c M hdis hlower
  have hsaving := dense_candidate_cost_saving M (Fintype.card V) (Nat.card core.ConnectedComponent)
    marks.card (edgeCost c (zoneCoreEdges zones)) (edgeCost c (old \ zoneCoreEdges zones)) (edgeCost c C)
    hM.le (by positivity) (by positivity) hcomponent hcore hcost
  have holdCost := kept_add_core_cost zones old c hsub
  refine ⟨C, hC, ?_, hmarks⟩
  linarith

end OnlineSteinerForest.UpperBound
