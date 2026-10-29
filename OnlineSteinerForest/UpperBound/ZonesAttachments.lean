import OnlineSteinerForest.Graph.Comparison
import OnlineSteinerForest.UpperBound.ZonesCost
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Actual connecting paths inside zones and the cost of their union. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V I : Type*} [DecidableEq V] [DecidableEq I]

/-- A zone supplies a simple connecting path using only its own original edges. -/
theorem exists_zone_attachment {G : SimpleGraph V} (c : Sym2 V → ℝ)
    (zone : Finset (Sym2 V)) (hinput : ∀ e ∈ zone, e ∈ G.edgeSet)
    (hc : ∀ e ∈ zone, 0 ≤ c e) {u v : V}
    (hreach : (SimpleGraph.fromEdgeSet (zone : Set (Sym2 V))).Reachable u v) :
    ∃ P : Finset (Sym2 V), IsPathEdges G u v P ∧ P ⊆ zone ∧
      edgeCost c P ≤ edgeCost c zone := by
  obtain ⟨P, hp, hsub⟩ := exists_pathEdges_subset hinput hreach
  exact ⟨P, hp, hsub, Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e he _ => hc e he)⟩

/-- Overlaps only reduce the original cost of the attachment union. -/
theorem attachment_union_cost_le (c : Sym2 V → ℝ) (indices : Finset I)
    (paths : I → Finset (Sym2 V)) (hc : ∀ i ∈ indices, ∀ e ∈ paths i, 0 ≤ c e) :
    edgeCost c (indices.biUnion paths) ≤ ∑ i ∈ indices, edgeCost c (paths i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [edgeCost]
  | @insert i indices hi ih =>
    rw [Finset.biUnion_insert, edgeCost_union, Finset.sum_insert hi]
    have hs : residualCost c (paths i) (indices.biUnion paths) ≤
        edgeCost c (indices.biUnion paths) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro e he _
      obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
      exact hc j (Finset.mem_insert_of_mem hj) e hej
    exact add_le_add le_rfl (hs.trans (ih (fun j hj => hc j (Finset.mem_insert_of_mem hj))))

/-- Each attachment costs at most the zone upper scale, counted once per exit. -/
theorem attachment_union_budget (c : Sym2 V → ℝ) (indices : Finset I)
    (paths : I → Finset (Sym2 V)) (budget : ℝ)
    (hc : ∀ i ∈ indices, ∀ e ∈ paths i, 0 ≤ c e)
    (hbudget : ∀ i ∈ indices, edgeCost c (paths i) ≤ budget) :
    edgeCost c (indices.biUnion paths) ≤ (indices.card : ℝ) * budget := by
  calc
    _ ≤ ∑ i ∈ indices, edgeCost c (paths i) := attachment_union_cost_le c indices paths hc
    _ ≤ ∑ _i ∈ indices, budget := Finset.sum_le_sum hbudget
    _ = _ := by simp

end OnlineSteinerForest.UpperBound
