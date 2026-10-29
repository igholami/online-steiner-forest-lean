import OnlineSteinerForest.Graph.Optimum

/-! Compare residual shortest paths with arbitrary feasible offline solutions. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- A feasible edge set supplies a simple input path contained in that set. -/
theorem exists_pathEdges_subset {G : SimpleGraph V} {s t : V}
    {F : Finset (Sym2 V)} (hF : ∀ e ∈ F, e ∈ G.edgeSet)
    (hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t) :
    ∃ P, IsPathEdges G s t P ∧ P ⊆ F := by
  classical
  let H := SimpleGraph.fromEdgeSet (F : Set (Sym2 V))
  have hle : H ≤ G := by
    intro u v huv
    exact hF _ huv.1
  obtain ⟨p, hp⟩ := hr.exists_isPath
  refine ⟨(p.mapLe hle).edges.toFinset, ⟨p.mapLe hle, hp.mapLe hle, rfl⟩, ?_⟩
  intro e he
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at he
  have hmem := p.edges_subset_edgeSet (List.mem_toFinset.mp he)
  exact (show e ∈ (F : Set (Sym2 V)) \ Sym2.diagSet by
    simpa only [SimpleGraph.edgeSet_fromEdgeSet] using hmem).1

/-- Residual shortest-path cost is at most any feasible comparison solution's cost. -/
theorem shortestPathEdges_cost_le {G : SimpleGraph V} (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V))
    (s t : V) (h : G.Reachable s t) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet)
    (hr : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t) :
    residualCost c B (shortestPathEdges G c B s t h) ≤ edgeCost c F := by
  obtain ⟨P, hP, hPF⟩ := exists_pathEdges_subset hF hr
  refine ((shortestPathEdges_spec G c B s t h).2 P hP).trans ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.sdiff_subset.trans hPF) (fun e he _ => hc e (hF e he))

end OnlineSteinerForest
