import OnlineSteinerForest.Graph.ForestOptimum

/-! The actual optimal forest used to initialize each batch class. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def initialReference (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : Finset (Sym2 V) :=
  (exists_optimal_forest G c hc requests feasible).choose

theorem initialReference_spec (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    FeasibleEdges G requests (initialReference G c hc requests feasible) ∧
      (SimpleGraph.fromEdgeSet ((initialReference G c hc requests feasible : Finset (Sym2 V)) :
        Set (Sym2 V))).IsAcyclic ∧
      edgeCost c (initialReference G c hc requests feasible) = optimum G c requests feasible :=
  (exists_optimal_forest G c hc requests feasible).choose_spec

end OnlineSteinerForest.UpperBound
