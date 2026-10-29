import OnlineSteinerForest.Graph.Optimum

/-! Nontrivial instances have positive optimum; no positivity is built into OPT. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*}

/-- A feasible solution of a nontrivial request cannot be empty. -/
theorem feasibleEdges_nonempty (G : SimpleGraph V) (requests : List (V × V))
    (F : Finset (Sym2 V)) (hF : FeasibleEdges G requests F)
    (q : V × V) (hq : q ∈ requests) (hne : q.1 ≠ q.2) : F.Nonempty := by
  by_contra he
  have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hr := hF.2 q hq
  simp only [hzero, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty,
    SimpleGraph.reachable_bot] at hr
  exact hne hr

variable [Fintype V]

/-- Strictly positive input costs imply strictly positive optimum for a nontrivial request. -/
theorem optimum_pos (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (q : V × V) (hq : q ∈ requests) (hne : q.1 ≠ q.2) :
    0 < optimum G c requests feasible := by
  have hF := optimalEdges_feasible G c requests feasible
  exact Finset.sum_pos (fun e he => hc e (hF.1 e he))
    (feasibleEdges_nonempty G requests _ hF q hq hne)

end OnlineSteinerForest
