import OnlineSteinerForest.Graph.Feasibility

/-! Residual shortest-path distances before and after purchases. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [DecidableEq V]

theorem residualCost_nonneg (c : Sym2 V → ℝ) (B F : Finset (Sym2 V))
    (hc : ∀ e ∈ F, 0 ≤ c e) : 0 ≤ residualCost c B F :=
  Finset.sum_nonneg (fun e he => hc e (Finset.mem_sdiff.mp he).1)

/-- More purchased edges can only decrease the cost of any fixed path. -/
theorem residualCost_antitone (c : Sym2 V → ℝ) (A B F : Finset (Sym2 V))
    (hc : ∀ e ∈ F, 0 ≤ c e) (hAB : A ⊆ B) :
    residualCost c B F ≤ residualCost c A F := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro e he
    simp only [Finset.mem_sdiff] at he ⊢
    exact ⟨he.1, fun heA => he.2 (hAB heA)⟩
  · intro e he _
    exact hc e (Finset.mem_sdiff.mp he).1

theorem residualCost_eq_zero_of_subset (c : Sym2 V → ℝ) (B F : Finset (Sym2 V))
    (h : F ⊆ B) : residualCost c B F = 0 := by
  simp [residualCost, Finset.sdiff_eq_empty_iff_subset.mpr h]

variable [Fintype V]

/-- The residual shortest-path distance, with feasibility made explicit. -/
noncomputable def residualDistance (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) : ℝ :=
  residualCost c B (shortestPathEdges G c B s t h)

theorem residualDistance_antitone (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (A B : Finset (Sym2 V)) (hAB : A ⊆ B)
    (s t : V) (h : G.Reachable s t) :
    residualDistance G c B s t h ≤ residualDistance G c A s t h := by
  have hpath := (shortestPathEdges_spec G c A s t h).1
  exact ((shortestPathEdges_spec G c B s t h).2 _ hpath).trans
    (residualCost_antitone c A B _
      (fun e he => hc e (hpath.subset_edgeSet e he)) hAB)

end OnlineSteinerForest
