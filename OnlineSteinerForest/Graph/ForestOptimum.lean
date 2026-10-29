import OnlineSteinerForest.Graph.Optimum
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! The minimum over feasible edge sets is attained by a genuine Steiner forest. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V]

/-- Deleting cycles preserves connectivity and cannot increase nonnegative cost.
Thus our finite edge-set minimization is exactly the manuscript's forest optimum. -/
theorem exists_optimal_forest (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    ∃ F : Finset (Sym2 V), FeasibleEdges G requests F ∧
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).IsAcyclic ∧
      edgeCost c F = optimum G c requests feasible := by
  classical
  let O := optimalEdges G c requests feasible
  let H := SimpleGraph.fromEdgeSet (O : Set (Sym2 V))
  have hO := optimalEdges_feasible G c requests feasible
  obtain ⟨T, hTH, hT, hreach⟩ := H.exists_isAcyclic_reachable_eq_le
  have hTO : T.edgeFinset ⊆ O := by
    intro e he
    have heH := (SimpleGraph.edgeSet_subset_edgeSet.mpr hTH)
      (SimpleGraph.mem_edgeFinset.mp he)
    exact (show e ∈ (O : Set (Sym2 V)) \ Sym2.diagSet by
      simpa only [H, SimpleGraph.edgeSet_fromEdgeSet] using heH).1
  have hfeas : FeasibleEdges G requests T.edgeFinset := by
    refine ⟨fun e he => hO.1 e (hTO he), ?_⟩
    intro q hq
    simp only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet]
    rw [hreach]
    exact hO.2 q hq
  refine ⟨T.edgeFinset, hfeas, ?_, ?_⟩
  · simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using hT
  · apply le_antisymm
    · exact Finset.sum_le_sum_of_subset_of_nonneg hTO
        (fun e he _ => hc e (hO.1 e he))
    · exact optimum_le G c requests feasible _ hfeas

end OnlineSteinerForest
