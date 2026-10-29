import OnlineSteinerForest.LowerBound.Trace.Compression
import OnlineSteinerForest.LowerBound.Trace.RunBound
import OnlineSteinerForest.LowerBound.RankBounds
import OnlineSteinerForest.LowerBound.TestComparison

/-! A bad rank supplies a short, simple, rank-distinct alternate route. -/
namespace OnlineSteinerForest.LowerBound.Trace

variable [OnlineSteinerForest.PathSelection]

theorem test_left_unmatched (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (i : Fin (matchingSize h)) :
    ∀ j ∈ testRanks h i, leftEndpoint σ i ≠ leftEndpoint σ j ∧
      leftEndpoint σ i ≠ rightEndpoint σ j := by
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact ⟨fun he => hji (leftEndpoint_injective σ he).symm, leftEndpoint_ne_right σ i j⟩

theorem test_right_unmatched (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (i : Fin (matchingSize h)) :
    ∀ j ∈ testRanks h i, rightEndpoint σ i ≠ leftEndpoint σ j ∧
      rightEndpoint σ i ≠ rightEndpoint σ j := by
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  exact ⟨(leftEndpoint_ne_right σ j i).symm,
    fun he => hji (rightEndpoint_injective σ he).symm⟩

theorem test_route_run_bound (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (i : Fin (matchingSize h))
    (r : Route σ (testRanks h i) (leftEndpoint σ i) (rightEndpoint σ i))
    (hr : r.realize.IsPath) : r.ranks.length + 1 ≤ r.baseSteps :=
  r.shortcut_count_add_one_le_baseSteps hr (endpoints_ne σ i)
    (test_left_unmatched h σ i) (test_right_unmatched h σ i)

theorem exists_route_of_bad_rank (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (i : Fin (matchingSize h)) (hbad : ¬ GoodRank h σ i) :
    ∃ r : Route σ (testRanks h i) (leftEndpoint σ i) (rightEndpoint σ i),
      r.realize.IsPath ∧ r.cost (testPrice h i) ≤ rankPrice h i := by
  let G := constructionGraph σ (testRanks h i)
  let c := constructionCost (testPrice h i)
  let reach := base_reachable σ (testRanks h i) (leftEndpoint σ i) (rightEndpoint σ i)
  have hd : residualDistance G c ∅ (Sum.inl (leftEndpoint σ i))
      (Sum.inl (rightEndpoint σ i)) reach ≤ rankPrice h i := le_of_not_gt hbad
  obtain ⟨p, hp, he⟩ := (shortestPathEdges_spec G c ∅ (Sum.inl (leftEndpoint σ i))
    (Sum.inl (rightEndpoint σ i)) reach).1
  obtain ⟨r, hr⟩ := exists_route_of_isPath σ (testRanks h i) _ _ p hp
  have hpr : r.realize.IsPath := by rw [hr]; exact hp
  refine ⟨r, hpr, ?_⟩
  have hc := r.edgeCost_realize (testPrice h i) hpr
  rw [hr, he] at hc
  change residualCost c ∅ _ ≤ rankPrice h i at hd
  rw [residualCost_empty, hc] at hd
  exact hd

theorem bad_route_size_bound (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (i : Fin (matchingSize h))
    (hi : firstRank h ≤ i.val + 1)
    (r : Route σ (testRanks h i) (leftEndpoint σ i) (rightEndpoint σ i))
    (hr : r.realize.IsPath) (hc : r.cost (testPrice h i) ≤ rankPrice h i) :
    r.ranks.length + 1 ≤ (logSize h) ^ 2 := by
  have hbase := r.baseSteps_le_cost (testPrice h i) (fun j _ => by
    unfold testPrice
    split_ifs
    · exact le_rfl
    · exact rankPrice_nonneg h j)
  have hsq : (r.baseSteps : ℝ) ≤ (logSize h : ℝ) ^ 2 :=
    hbase.trans (hc.trans (rankPrice_le_logSize_sq h hh i hi))
  have hn : r.baseSteps ≤ (logSize h) ^ 2 := by exact_mod_cast hsq
  exact (test_route_run_bound h σ i r hr).trans hn

end OnlineSteinerForest.LowerBound.Trace
