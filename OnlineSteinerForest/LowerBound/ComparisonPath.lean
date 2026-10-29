import OnlineSteinerForest.LowerBound.PathEnumeration
import OnlineSteinerForest.LowerBound.Connectivity
import OnlineSteinerForest.Graph.Optimum

/-! The comparison path is a feasible offline solution of cost `2*m - 1`. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

variable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m))

theorem comparisonEdges_input : ∀ e ∈ comparisonEdges m, e ∈ (constructionGraph σ R).edgeSet := by
  intro e he
  rw [constructionGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨Finset.mem_union_left _ he, ?_⟩
  obtain ⟨⟨u, v⟩, huv, rfl⟩ := Finset.mem_image.mp he
  intro hdiag
  have heq : Sum.inl u = (Sum.inl v : Vertex m) := Sym2.mk_isDiag_iff.mp hdiag
  have hv := congrArg Fin.val (Sum.inl.inj heq)
  have h := (Finset.mem_filter.mp huv).2
  change u.val + 1 = v.val ∨ v.val + 1 = u.val at h
  omega

theorem comparisonEdges_feasible :
    FeasibleEdges (constructionGraph σ R) (requestedPairs σ R) (comparisonEdges m) := by
  refine ⟨comparisonEdges_input σ R, ?_⟩
  intro q hq
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
  have hr := base_reachable σ ∅ (leftEndpoint σ i) (rightEndpoint σ i)
  simpa only [constructionGraph, constructionEdges, Finset.biUnion_empty,
    Finset.union_empty] using hr

theorem comparisonEdges_cost (w : Fin m → ℝ) :
    edgeCost (constructionCost w) (comparisonEdges m) = (2 * m - 1 : ℕ) := by
  calc
    _ = ∑ _e ∈ comparisonEdges m, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨⟨u, v⟩, _, rfl⟩ := Finset.mem_image.mp he
      rfl
    _ = _ := by simp [comparisonEdges_card]

end OnlineSteinerForest.LowerBound
