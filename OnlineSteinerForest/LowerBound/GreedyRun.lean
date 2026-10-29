import OnlineSteinerForest.LowerBound.GreedyStep

/-! Iterate the exact good-rank step along an increasing request sequence. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

def rankRequests {m : ℕ} (σ : Equiv.Perm (Fin (2 * m))) (xs : List (Fin m)) :
    List (Vertex m × Vertex m) :=
  xs.map (fun i => (Sum.inl (leftEndpoint σ i), Sum.inl (rightEndpoint σ i)))

theorem greedy_rank_list (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (R : Finset (Fin (matchingSize h))) (xs : List (Fin (matchingSize h)))
    (hR : ∀ i ∈ xs, i ∈ R) (hgood : ∀ i ∈ xs, GoodRank h σ i)
    (horder : xs.Pairwise (· < ·)) (S : Finset (Fin (matchingSize h)))
    (hbefore : ∀ j ∈ S, ∀ i ∈ xs, j < i)
    (feasible : ∀ q ∈ rankRequests σ xs, (constructionGraph σ R).Reachable q.1 q.2) :
    greedy (constructionGraph σ R) (constructionCost (rankPrice h))
      (rankRequests σ xs) feasible (S.biUnion (matchingEdges σ)) =
      (S ∪ xs.toFinset).biUnion (matchingEdges σ) := by
  induction xs generalizing S with
  | nil => simp [rankRequests]
  | cons i xs ih =>
    have hiR : i ∈ R := hR i (by simp)
    have hgi : GoodRank h σ i := hgood i (by simp)
    have hSi : ∀ j ∈ S, j < i := fun j hj => hbefore j hj i (by simp)
    have hhead := shortestPathEdges_at_good_rank h σ R S i hiR hSi hgi
    have htailR : ∀ j ∈ xs, j ∈ R := fun j hj => hR j (by simp [hj])
    have htailgood : ∀ j ∈ xs, GoodRank h σ j := fun j hj => hgood j (by simp [hj])
    have htailorder : xs.Pairwise (· < ·) := (List.pairwise_cons.mp horder).2
    have htailbefore : ∀ j ∈ insert i S, ∀ k ∈ xs, j < k := by
      intro j hj k hk
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (List.pairwise_cons.mp horder).1 k hk
      · exact hbefore j hj k (by simp [hk])
    have hB : S.biUnion (matchingEdges σ) ∪ matchingEdges σ i =
        (insert i S).biUnion (matchingEdges σ) := by
      simp [Finset.biUnion_insert, Finset.union_comm]
    change ∀ q ∈ ((Sum.inl (leftEndpoint σ i), Sum.inl (rightEndpoint σ i)) ::
      rankRequests σ xs), (constructionGraph σ R).Reachable q.1 q.2 at feasible
    change greedy (constructionGraph σ R) (constructionCost (rankPrice h))
      ((Sum.inl (leftEndpoint σ i), Sum.inl (rightEndpoint σ i)) :: rankRequests σ xs)
      feasible (S.biUnion (matchingEdges σ)) = _
    rw [greedy.eq_def]
    dsimp only [greedyStep]
    rw [hhead, hB]
    rw [ih htailR htailgood htailorder (insert i S) htailbefore]
    congr 1
    ext j
    simp

end OnlineSteinerForest.LowerBound
