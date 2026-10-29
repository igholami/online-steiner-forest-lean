import OnlineSteinerForest.UpperBound.ZonesInterstarRetained
import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary
import OnlineSteinerForest.Graph.Feasibility

/-! The replacement skeleton is the union of actual selected realizing paths and full zones. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {centers : Finset V} {stars : StarContraction G centers}

structure ZoneSkeletonData (f : InterstarForest stars) (ambient : SimpleGraph W)
    (zones : V → Finset (Sym2 W)) where
  left : f.Link → W
  right : f.Link → W
  paths : f.Link → Finset (Sym2 W)
  left_mem : ∀ i, zoneSupport (zones (f.linkLeft i)) (left i)
  right_mem : ∀ i, zoneSupport (zones (f.linkRight i)) (right i)
  path : ∀ i, IsPathEdges ambient (left i) (right i) (paths i)

namespace ZoneSkeletonData
variable {f : InterstarForest stars} {ambient : SimpleGraph W} {zones : V → Finset (Sym2 W)}

noncomputable def edges (d : ZoneSkeletonData f ambient zones) : Finset (Sym2 W) :=
  f.retainedZones.biUnion zones ∪ Finset.univ.biUnion d.paths

theorem zone_subset (d : ZoneSkeletonData f ambient zones) (v : V) (hv : v ∈ f.retainedZones) :
    zones v ⊆ d.edges := by
  intro e he
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨v, hv, he⟩)

theorem path_subset (d : ZoneSkeletonData f ambient zones) (i : f.Link) : d.paths i ⊆ d.edges := by
  intro e he
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, he⟩)

theorem input_edges (d : ZoneSkeletonData f ambient zones)
    (hz : ∀ v, ∀ e ∈ zones v, e ∈ ambient.edgeSet) : ∀ e ∈ d.edges, e ∈ ambient.edgeSet := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨v, hv, he⟩ := Finset.mem_biUnion.mp he
    exact hz v e he
  · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    exact (d.path i).subset_edgeSet e he

theorem path_reachable (d : ZoneSkeletonData f ambient zones) (i : f.Link) :
    (SimpleGraph.fromEdgeSet (d.edges : Set (Sym2 W))).Reachable (d.left i) (d.right i) :=
  (d.path i).reachable.mono (fromEdges_mono (d.path_subset i))

end ZoneSkeletonData
end OnlineSteinerForest.UpperBound
