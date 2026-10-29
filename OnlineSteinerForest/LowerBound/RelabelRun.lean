import OnlineSteinerForest.LowerBound.RelabelUnique
import OnlineSteinerForest.LowerBound.GreedyRun
import OnlineSteinerForest.Graph.RelabelFeasibility

/-! Exact matching-edge purchases remain true after relabeling this unique-path instance. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W : Type} [Fintype W] [DecidableEq W]

def relabelRankRequests (h : ℕ) (e : Vertex (matchingSize h) ≃ W)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (xs : List (Fin (matchingSize h))) :=
  xs.map (fun i => (e (Sum.inl (leftEndpoint σ i)), e (Sum.inl (rightEndpoint σ i))))

theorem relabel_shortest_at_good_rank (h : ℕ) (e : Vertex (matchingSize h) ≃ W)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (R S : Finset (Fin (matchingSize h)))
    (i : Fin (matchingSize h)) (hi : i ∈ R) (hS : ∀ j ∈ S, j < i) (hgood : GoodRank h σ i)
    (hr : ((constructionGraph σ R).map e).Reachable
      (e (Sum.inl (leftEndpoint σ i))) (e (Sum.inl (rightEndpoint σ i)))) :
    shortestPathEdges ((constructionGraph σ R).map e) (relabelCost e (constructionCost (rankPrice h)))
      (relabelEdges e (S.biUnion (matchingEdges σ))) (e (Sum.inl (leftEndpoint σ i)))
      (e (Sum.inl (rightEndpoint σ i))) hr = relabelEdges e (matchingEdges σ i) :=
  shortestPathEdges_map_of_unique (SimpleGraph.Iso.map e _) _ _ _ _ _
    (matchingEdges_isPathEdges σ R i hi) (matching_path_unique h σ R S i hS hgood) hr

theorem greedy_relabel_rank_list (h : ℕ) (e : Vertex (matchingSize h) ≃ W)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (R : Finset (Fin (matchingSize h)))
    (xs : List (Fin (matchingSize h))) (hR : ∀ i ∈ xs, i ∈ R)
    (hgood : ∀ i ∈ xs, GoodRank h σ i) (horder : xs.Pairwise (· < ·))
    (S : Finset (Fin (matchingSize h))) (hbefore : ∀ j ∈ S, ∀ i ∈ xs, j < i)
    (feasible : ∀ q ∈ relabelRankRequests h e σ xs,
      ((constructionGraph σ R).map e).Reachable q.1 q.2) :
    greedy ((constructionGraph σ R).map e) (relabelCost e (constructionCost (rankPrice h)))
      (relabelRankRequests h e σ xs) feasible (relabelEdges e (S.biUnion (matchingEdges σ))) =
      relabelEdges e ((S ∪ xs.toFinset).biUnion (matchingEdges σ)) := by
  induction xs generalizing S with
  | nil => simp [relabelRankRequests]
  | cons i xs ih =>
    have hiR : i ∈ R := hR i (by simp)
    have hgi : GoodRank h σ i := hgood i (by simp)
    have hSi : ∀ j ∈ S, j < i := fun j hj => hbefore j hj i (by simp)
    have htailR : ∀ j ∈ xs, j ∈ R := fun j hj => hR j (by simp [hj])
    have htailgood : ∀ j ∈ xs, GoodRank h σ j := fun j hj => hgood j (by simp [hj])
    have htailorder : xs.Pairwise (· < ·) := (List.pairwise_cons.mp horder).2
    have htailbefore : ∀ j ∈ insert i S, ∀ k ∈ xs, j < k := by
      intro j hj k hk
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (List.pairwise_cons.mp horder).1 k hk
      · exact hbefore j hj k (by simp [hk])
    have hB : relabelEdges e (S.biUnion (matchingEdges σ)) ∪ relabelEdges e (matchingEdges σ i) =
        relabelEdges e ((insert i S).biUnion (matchingEdges σ)) := by
      rw [← relabelEdges_union]
      congr 1
      simp [Finset.biUnion_insert, Finset.union_comm]
    change ∀ q ∈ ((e (Sum.inl (leftEndpoint σ i)), e (Sum.inl (rightEndpoint σ i))) ::
      relabelRankRequests h e σ xs), ((constructionGraph σ R).map e).Reachable q.1 q.2 at feasible
    change greedy _ _ ((e (Sum.inl (leftEndpoint σ i)), e (Sum.inl (rightEndpoint σ i))) ::
      relabelRankRequests h e σ xs) feasible _ = _
    unfold greedy
    dsimp only [greedyStep]
    rw [relabel_shortest_at_good_rank h e σ R S i hiR hSi hgi, hB]
    rw [ih htailR htailgood htailorder (insert i S) htailbefore]
    congr 2
    ext j
    simp

end OnlineSteinerForest.LowerBound
