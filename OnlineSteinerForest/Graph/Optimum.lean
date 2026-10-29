import OnlineSteinerForest.Graph.Feasibility

/-! The offline optimum is a genuine finite minimization over feasible input edges. -/
namespace OnlineSteinerForest

variable {V : Type*} [Fintype V]

noncomputable def offlineCandidates (G : SimpleGraph V) (requests : List (V × V)) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.filter (FeasibleEdges G requests)

@[simp] theorem mem_offlineCandidates (G : SimpleGraph V) (requests : List (V × V))
    (F : Finset (Sym2 V)) :
    F ∈ offlineCandidates G requests ↔ FeasibleEdges G requests F := by
  classical
  simp [offlineCandidates]

theorem offlineCandidates_nonempty (G : SimpleGraph V) (requests : List (V × V))
    (h : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    (offlineCandidates G requests).Nonempty := by
  classical
  refine ⟨G.edgeFinset, (mem_offlineCandidates _ _ _).2 ⟨?_, ?_⟩⟩
  · intro e he
    exact G.mem_edgeFinset.mp he
  · intro q hq
    simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using h q hq

/-- A minimum-cost offline solution. Cycles are allowed in the search; positive
costs ensure that they cannot improve the optimum over Steiner forests. -/
noncomputable def optimalEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (h : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    Finset (Sym2 V) :=
  Classical.choose ((offlineCandidates G requests).exists_min_image
    (edgeCost c) (offlineCandidates_nonempty G requests h))

/-- The true offline optimum, independent of any upper/lower-bound certificate. -/
noncomputable def optimum (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (h : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℝ :=
  edgeCost c (optimalEdges G c requests h)

theorem optimalEdges_feasible (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (h : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    FeasibleEdges G requests (optimalEdges G c requests h) := by
  exact (mem_offlineCandidates _ _ _).1
    (Classical.choose_spec ((offlineCandidates G requests).exists_min_image
      (edgeCost c) (offlineCandidates_nonempty G requests h))).1

theorem optimum_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (h : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (F : Finset (Sym2 V)) (hF : FeasibleEdges G requests F) :
    optimum G c requests h ≤ edgeCost c F := by
  exact (Classical.choose_spec ((offlineCandidates G requests).exists_min_image
    (edgeCost c) (offlineCandidates_nonempty G requests h))).2 F
      ((mem_offlineCandidates _ _ _).2 hF)

end OnlineSteinerForest
