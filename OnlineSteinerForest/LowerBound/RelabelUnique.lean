import OnlineSteinerForest.LowerBound.GreedyStep
import OnlineSteinerForest.Graph.RelabelShortest

/-! The lower-bound matching path is the unique minimizing edge set at a good rank. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem matching_path_unique (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (R S : Finset (Fin (matchingSize h)))
    (i : Fin (matchingSize h)) (hS : ∀ j ∈ S, j < i) (hgood : GoodRank h σ i)
    (F : Finset (Sym2 (Vertex (matchingSize h))))
    (hF : IsPathEdges (constructionGraph σ R) (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) F)
    (hle : residualCost (constructionCost (rankPrice h)) (S.biUnion (matchingEdges σ)) F ≤
      residualCost (constructionCost (rankPrice h)) (S.biUnion (matchingEdges σ)) (matchingEdges σ i)) :
    F = matchingEdges σ i := by
  have hpay : residualCost (constructionCost (rankPrice h))
      (S.biUnion (matchingEdges σ)) (matchingEdges σ i) = rankPrice h i := by
    rw [residualCost, (matching_disjoint_previous h σ S i hS).sdiff_eq_left]
    exact matchingEdges_cost σ _ i
  rw [hpay] at hle
  rcases pathEdges_eq_or_disjoint σ R i F hF with heq | hd
  · exact heq
  · exact False.elim (not_lt_of_ge hle
      (good_rank_alternative_cost h σ R S i hS hgood F hF hd))

end OnlineSteinerForest.LowerBound
