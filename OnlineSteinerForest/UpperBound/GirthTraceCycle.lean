import OnlineSteinerForest.UpperBound.GirthTraceEncoding
import OnlineSteinerForest.UpperBound.GirthTraceChain
import OnlineSteinerForest.UpperBound.GirthTraceCost

/-! Final conversion from transported labelled walks to a standard mathlib cycle. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem cycle_of_distinct_traces (left right : I → V) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    {u v : V} (ds es : List (Dart I)) (hd : TraceValid left right u v ds)
    (he : TraceValid left right u v es) (hnbd : TraceNonbacktracking ds)
    (hnbe : TraceNonbacktracking es) (hne : ds ≠ es) :
    ∃ z, ∃ c : (edgeSubdivision left right).Walk z z, c.IsCycle ∧
      (c.edges.map (subdivisionCost w)).sum ≤ traceCost w ds + traceCost w es := by
  let P := traceWalk left right ds hd
  let Q := traceWalk left right es he
  have hPQ : P ≠ Q := by
    intro h
    exact hne (traceWalk_support_injective left right ds es hd he (congrArg SimpleGraph.Walk.support h))
  obtain ⟨z, c, hc, hcost⟩ := cycle_cost_in_two_walks P Q hPQ
    (traceWalk_chain left right ds hd hnbd) (traceWalk_chain left right es he hnbe)
    (subdivisionCost w) (subdivisionCost_nonneg w hw)
  exact ⟨z, c, hc, by simpa only [P, Q, traceWalk_cost] using hcost⟩

end OnlineSteinerForest.UpperBound.Girth
