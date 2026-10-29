import OnlineSteinerForest.UpperBound.GirthLabelledWalks
import OnlineSteinerForest.UpperBound.GirthSubdivisionCost

/-! Exact original-edge cost of an arbitrary labelled walk after simple subdivision. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem traceWalk_cost (left right : I → V) (w : I → ℝ) {u v : V}
    (ds : List (Dart I)) (h : TraceValid left right u v ds) :
    ((traceWalk left right ds h).edges.map (subdivisionCost w)).sum = traceCost w ds := by
  induction ds generalizing u with
  | nil => simp [traceWalk, traceCost]
  | cons d ds ih =>
    change ((((dartWalk left right d).append (traceWalk left right ds h.2)).copy _ _).edges.map
      (subdivisionCost w)).sum = _
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_append, List.map_append,
      List.sum_append, dartWalk_cost, ih]
    rfl

end OnlineSteinerForest.UpperBound.Girth
