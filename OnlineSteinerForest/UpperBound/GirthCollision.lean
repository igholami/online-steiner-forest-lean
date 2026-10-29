import OnlineSteinerForest.UpperBound.GirthTraceCycle

/-! The induction witness for graph reduction is a pair of distinct reduced walks. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

structure Collision (left right : I → V) where
  start : V
  finish : V
  firstTrace : List (Dart I)
  secondTrace : List (Dart I)
  firstValid : TraceValid left right start finish firstTrace
  secondValid : TraceValid left right start finish secondTrace
  firstNonbacktracking : TraceNonbacktracking firstTrace
  secondNonbacktracking : TraceNonbacktracking secondTrace
  distinct : firstTrace ≠ secondTrace

noncomputable def Collision.cost {left right : I → V} (p : Collision left right) (w : I → ℝ) : ℝ :=
  traceCost w p.firstTrace + traceCost w p.secondTrace

variable [Fintype I] [DecidableEq I] [DecidableEq V]

theorem Collision.exists_cycle {left right : I → V} (p : Collision left right)
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ z, ∃ c : (edgeSubdivision left right).Walk z z, c.IsCycle ∧
      (c.edges.map (subdivisionCost w)).sum ≤ p.cost w :=
  cycle_of_distinct_traces left right w hw p.firstTrace p.secondTrace p.firstValid p.secondValid
    p.firstNonbacktracking p.secondNonbacktracking p.distinct

end OnlineSteinerForest.UpperBound.Girth
