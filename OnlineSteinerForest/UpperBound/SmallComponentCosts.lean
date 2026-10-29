import OnlineSteinerForest.UpperBound.SmallComponentEdges
import OnlineSteinerForest.UpperBound.ZonesCost

/-! Exact cost decomposition over the reference graph's ordinary connected components. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def referenceComponents (G : SimpleGraph V) : Finset G.ConnectedComponent :=
  Finset.univ.image G.connectedComponentMk

theorem componentEdges_disjoint (G : SimpleGraph V) :
    (referenceComponents G : Set G.ConnectedComponent).PairwiseDisjoint (componentEdges G) := by
  intro C _ D _ hCD
  apply Finset.disjoint_left.mpr
  intro e heC heD
  induction e using Sym2.ind with
  | _ u v =>
    have hc := ((mem_componentEdges G C u v).mp heC).2
    have hd := ((mem_componentEdges G D u v).mp heD).2
    exact hCD (hc.symm.trans hd)

theorem componentEdges_union (G : SimpleGraph V) :
    (referenceComponents G).biUnion (componentEdges G) = G.edgeFinset := by
  apply Finset.Subset.antisymm
  · intro e he
    obtain ⟨C, _, hC⟩ := Finset.mem_biUnion.mp he
    exact componentEdges_subset G C hC
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      refine Finset.mem_biUnion.mpr ⟨G.connectedComponentMk u,
        Finset.mem_image_of_mem _ (Finset.mem_univ u), ?_⟩
      exact (mem_componentEdges G _ u v).mpr ⟨SimpleGraph.mem_edgeFinset.mp he, rfl⟩

theorem sum_component_costs (G : SimpleGraph V) (c : Sym2 V → ℝ) :
    (∑ C ∈ referenceComponents G, edgeCost c (componentEdges G C)) = edgeCost c G.edgeFinset := by
  simpa only [componentEdges_union] using
    zone_cost_sum c (referenceComponents G) (componentEdges G) (componentEdges_disjoint G)

end OnlineSteinerForest.UpperBound
