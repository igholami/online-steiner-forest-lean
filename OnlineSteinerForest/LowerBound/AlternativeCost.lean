import OnlineSteinerForest.LowerBound.TestComparison
import OnlineSteinerForest.LowerBound.Paths

/-! Every alternate path at a good rank costs strictly more than that rank's route. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem test_cost_zero_on_previous (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (S : Finset (Fin (matchingSize h)))
    (i : Fin (matchingSize h)) (hS : ∀ j ∈ S, j < i)
    (e : Sym2 (Vertex (matchingSize h))) (he : e ∈ S.biUnion (matchingEdges σ)) :
    constructionCost (testPrice h i) e = 0 := by
  obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp he
  rw [constructionCost_of_mem_matching σ _ j e hej]
  simp [testPrice, hS j hj]

theorem good_rank_alternative_cost (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (R S : Finset (Fin (matchingSize h)))
    (i : Fin (matchingSize h)) (hS : ∀ j ∈ S, j < i) (hgood : GoodRank h σ i)
    (P : Finset (Sym2 (Vertex (matchingSize h))))
    (hP : IsPathEdges (constructionGraph σ R) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) P) (hd : Disjoint P (matchingEdges σ i)) :
    rankPrice h i < residualCost (constructionCost (rankPrice h))
      (S.biUnion (matchingEdges σ)) P := by
  have htest := alternate_path_in_test σ R i P hP hd
  have hmin := (shortestPathEdges_spec (constructionGraph σ (testRanks h i))
    (constructionCost (testPrice h i)) ∅ (Sum.inl (leftEndpoint σ i))
    (Sum.inl (rightEndpoint σ i)) (base_reachable σ (testRanks h i) _ _)).2 P htest
  have hdist : residualDistance (constructionGraph σ (testRanks h i))
      (constructionCost (testPrice h i)) ∅ (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) (base_reachable σ (testRanks h i) _ _) ≤
      edgeCost (constructionCost (testPrice h i)) P := by
    simpa only [residualDistance, residualCost_empty] using hmin
  have hcost : edgeCost (constructionCost (testPrice h i)) P ≤
      residualCost (constructionCost (rankPrice h)) (S.biUnion (matchingEdges σ)) P := by
    apply edgeCost_le_residualCost
    · intro e _ he
      exact (test_cost_zero_on_previous h σ S i hS e he).le
    · intro e _ _
      exact constructionCost_mono _ _ (testPrice_le h i) e
  exact hgood.trans_le (hdist.trans hcost)

end OnlineSteinerForest.LowerBound
