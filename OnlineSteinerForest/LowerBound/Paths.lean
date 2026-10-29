import OnlineSteinerForest.LowerBound.EdgeStructure
import OnlineSteinerForest.Graph.DegreeTwo

/-! A simple path either uses the designated matching route or avoids both of its edges. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

variable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (R : Finset (Fin m))

theorem matchingEdges_isPathEdges (i : Fin m) (hi : i ∈ R) :
    IsPathEdges (constructionGraph σ R) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) (matchingEdges σ i) := by
  have hl := ((subdivision_adj σ R i (Sum.inl (leftEndpoint σ i))).mpr
    ⟨hi, Or.inl rfl⟩).symm
  have hr := (subdivision_adj σ R i (Sum.inl (rightEndpoint σ i))).mpr ⟨hi, Or.inr rfl⟩
  refine ⟨SimpleGraph.Walk.cons hl (SimpleGraph.Walk.cons hr SimpleGraph.Walk.nil), ?_, ?_⟩
  · simp [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.support_cons, endpoints_ne σ i]
  · simp [matchingEdges]

theorem pathEdges_eq_or_disjoint (i : Fin m) (P : Finset (Sym2 (Vertex m)))
    (hP : IsPathEdges (constructionGraph σ R) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) P) :
    P = matchingEdges σ i ∨ Disjoint P (matchingEdges σ i) := by
  obtain ⟨p, hp, rfl⟩ := hP
  by_cases hmem : s(Sum.inl (leftEndpoint σ i), Sum.inr i) ∈ p.edges ∨
      s(Sum.inr i, Sum.inl (rightEndpoint σ i)) ∈ p.edges
  · left
    exact path_edges_eq_pair_of_mem_either
      (by simpa using endpoints_ne σ i) (by simp) (by simp)
      (fun z hz => (subdivision_adj σ R i z).mp hz |>.2) p hp hmem
  · right
    apply Finset.disjoint_left.mpr
    intro e he hm
    simp only [matchingEdges, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl
    · exact hmem (Or.inl (List.mem_toFinset.mp he))
    · exact hmem (Or.inr (List.mem_toFinset.mp he))

end OnlineSteinerForest.LowerBound
