import OnlineSteinerForest.LowerBound.Tests
import OnlineSteinerForest.LowerBound.EdgeStructure
import OnlineSteinerForest.Graph.ResidualComparison

/-! The rank-test graph is a lower-cost supergraph of every actual alternate route. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

variable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m)))

theorem alternate_edge_in_test (R : Finset (Fin m)) (i : Fin m) (e : Sym2 (Vertex m))
    (he : e ∈ (constructionGraph σ R).edgeSet) (hn : e ∉ matchingEdges σ i) :
    e ∈ (constructionGraph σ (Finset.univ.erase i)).edgeSet := by
  have he' : e ∈ (constructionEdges σ R : Set _) \ Sym2.diagSet := by
    simpa only [constructionGraph, SimpleGraph.edgeSet_fromEdgeSet] using he
  rw [constructionGraph, SimpleGraph.edgeSet_fromEdgeSet]
  refine ⟨?_, he'.2⟩
  rcases Finset.mem_union.mp he'.1 with he | he
  · exact Finset.mem_union_left _ he
  · obtain ⟨j, _, hej⟩ := Finset.mem_biUnion.mp he
    have hji : j ≠ i := by intro h; subst j; exact hn hej
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩, hej⟩)

theorem alternate_path_in_test (R : Finset (Fin m)) (i : Fin m) (P : Finset (Sym2 (Vertex m)))
    (hP : IsPathEdges (constructionGraph σ R) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) P) (hd : Disjoint P (matchingEdges σ i)) :
    IsPathEdges (constructionGraph σ (Finset.univ.erase i)) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) P := by
  obtain ⟨p, hp, rfl⟩ := hP
  have htrans : ∀ e ∈ p.edges, e ∈ (constructionGraph σ (Finset.univ.erase i)).edgeSet := by
    intro e he
    exact alternate_edge_in_test σ R i e (p.edges_subset_edgeSet he)
      (fun hm => Finset.disjoint_left.mp hd (List.mem_toFinset.mpr he) hm)
  refine ⟨p.transfer _ htrans, hp.transfer htrans, ?_⟩
  simp

theorem constructionCost_mono (w z : Fin m → ℝ) (h : ∀ i, w i ≤ z i)
    (e : Sym2 (Vertex m)) : constructionCost w e ≤ constructionCost z e := by
  refine Sym2.ind (fun u v => ?_) e
  cases u <;> cases v <;> simp only [constructionCost_base, constructionCost_left,
    constructionCost_right, constructionCost_private]
  · rfl
  · exact div_le_div_of_nonneg_right (h _) (by positivity)
  · exact div_le_div_of_nonneg_right (h _) (by positivity)
  · rfl

theorem constructionCost_of_mem_matching (w : Fin m → ℝ) (i : Fin m)
    (e : Sym2 (Vertex m)) (he : e ∈ matchingEdges σ i) : constructionCost w e = w i / 2 := by
  simp only [matchingEdges, Finset.mem_insert, Finset.mem_singleton] at he
  rcases he with rfl | rfl <;> simp

theorem rankPrice_nonneg (h : ℕ) (i : Fin (matchingSize h)) : 0 ≤ rankPrice h i := by
  unfold rankPrice
  exact_mod_cast price_nonneg h (i.val + 1)

theorem testPrice_le (h : ℕ) (i j : Fin (matchingSize h)) : testPrice h i j ≤ rankPrice h j := by
  unfold testPrice
  split_ifs
  · exact rankPrice_nonneg h j
  · rfl

end OnlineSteinerForest.LowerBound
