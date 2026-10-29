import OnlineSteinerForest.UpperBound.NearestNeighborWalkCost

/-! Residual shortest-path distances are bounded by original walk lengths. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {α : Type*} [DecidableEq α]

theorem sum_toFinset_le_sum_map (l : List α) (f : α → ℝ) (hf : ∀ a ∈ l, 0 ≤ f a) :
    (∑ a ∈ l.toFinset, f a) ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hfl : ∀ b ∈ l, 0 ≤ f b := fun b hb => hf b (by simp [hb])
    have hfa : 0 ≤ f a := hf a (by simp)
    have hi := ih hfl
    by_cases ha : a ∈ l
    · simp only [List.toFinset_cons, Finset.insert_eq_of_mem (List.mem_toFinset.mpr ha),
        List.map_cons, List.sum_cons]
      linarith
    · have ha' : a ∉ l.toFinset := by simpa using ha
      rw [List.toFinset_cons, Finset.sum_insert ha']
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add le_rfl hi

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem residualDistance_le_walkCost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (s t : V) (hst : G.Reachable s t) (p : G.Walk s t) :
    residualDistance G c ∅ s t hst ≤ walkCost c p := by
  have hp : IsPathEdges G s t p.toPath.val.edges.toFinset :=
    ⟨p.toPath.val, p.toPath.prop, rfl⟩
  have hsub : p.toPath.val.edges.toFinset ⊆ p.edges.toFinset := by
    intro e he
    exact List.mem_toFinset.mpr (p.edges_toPath_subset_edges (List.mem_toFinset.mp he))
  have hmono := residualCost_mono_edges c ∅ _ _ hsub
    (fun e he => hc e (p.edges_subset_edgeSet (List.mem_toFinset.mp he)))
  have hmin := (shortestPathEdges_spec G c ∅ s t hst).2 _ hp
  calc
    _ ≤ edgeCost c p.toPath.val.edges.toFinset := by
      simpa only [residualDistance, residualCost_empty] using hmin
    _ ≤ edgeCost c p.edges.toFinset := by simpa only [residualCost_empty] using hmono
    _ ≤ walkCost c p := sum_toFinset_le_sum_map p.edges c (fun e he => hc e (p.edges_subset_edgeSet he))

end OnlineSteinerForest.UpperBound
