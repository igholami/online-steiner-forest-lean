import OnlineSteinerForest.UpperBound.ZonesForestComponentPartition
import OnlineSteinerForest.UpperBound.ZonesForestLargeComponents
import OnlineSteinerForest.UpperBound.ZonesForestJoin

/-! All large reference components share one ambient subdivision and one cost function. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem uniform_large_forest_partition (F : SimpleGraph V) (hF : F.IsAcyclic) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (hbound : ∀ e ∈ subdivisionEdges F.edgeFinset n, subdivisionCost c n e ≤ M) :
    Nonempty (ZonePartition (subdivisionEdges (largeForestEdges F c M) n) (subdivisionCost c n) M) := by
  let indices := largeForestComponents F c M
  let E := fun C : F.ConnectedComponent => subdivisionEdges (componentEdges F C) n
  let P : (i : ↥indices) → ZonePartition (E i.val) (subdivisionCost c n) M := fun i =>
    Classical.choice (uniform_component_partition F hF c hc M hM n hbound i.val (Finset.mem_filter.mp i.property).2)
  have hdis : (indices : Set F.ConnectedComponent).PairwiseDisjoint E := by
    intro C hC D hD hCD
    exact subdivisionEdges_disjoint (componentEdges_disjoint F
      (Finset.mem_filter.mp hC).1 (Finset.mem_filter.mp hD).1 hCD) n
  have hp : Nonempty (ZonePartition (indices.biUnion E) (subdivisionCost c n) M) :=
    ⟨joinZonePartitions indices E (subdivisionCost c n) M P hdis⟩
  simpa only [indices, E, largeForestEdges, subdivisionEdges_biUnion] using hp

end OnlineSteinerForest.UpperBound
