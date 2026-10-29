import OnlineSteinerForest.LowerBound.AlternativeCost
import OnlineSteinerForest.Greedy.Algorithm

/-! Exact behavior of the implemented shortest-path selection at one good rank. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem matching_disjoint_previous (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (S : Finset (Fin (matchingSize h)))
    (i : Fin (matchingSize h)) (hS : ∀ j ∈ S, j < i) :
    Disjoint (matchingEdges σ i) (S.biUnion (matchingEdges σ)) := by
  apply Finset.disjoint_left.mpr
  intro e hei heS
  obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp heS
  exact Finset.disjoint_left.mp (matchingEdges_disjoint σ (ne_of_gt (hS j hj))) hei hej

theorem shortestPathEdges_at_good_rank (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (R S : Finset (Fin (matchingSize h)))
    (i : Fin (matchingSize h)) (hi : i ∈ R) (hS : ∀ j ∈ S, j < i)
    (hgood : GoodRank h σ i) :
    shortestPathEdges (constructionGraph σ R) (constructionCost (rankPrice h))
      (S.biUnion (matchingEdges σ)) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) (base_reachable σ R _ _) = matchingEdges σ i := by
  have hspec := shortestPathEdges_spec (constructionGraph σ R) (constructionCost (rankPrice h))
    (S.biUnion (matchingEdges σ)) (Sum.inl (leftEndpoint σ i))
    (Sum.inl (rightEndpoint σ i)) (base_reachable σ R _ _)
  have hpay : residualCost (constructionCost (rankPrice h))
      (S.biUnion (matchingEdges σ)) (matchingEdges σ i) = rankPrice h i := by
    rw [residualCost, (matching_disjoint_previous h σ S i hS).sdiff_eq_left]
    exact matchingEdges_cost σ _ i
  have hle := hspec.2 _ (matchingEdges_isPathEdges σ R i hi)
  rw [hpay] at hle
  rcases pathEdges_eq_or_disjoint σ R i _ hspec.1 with heq | hd
  · exact heq
  · have hgt := good_rank_alternative_cost h σ R S i hS hgood _ hspec.1 hd
    exact False.elim (not_lt_of_ge hle hgt)

end OnlineSteinerForest.LowerBound
