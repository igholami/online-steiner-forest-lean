import OnlineSteinerForest.UpperBound.GirthLabelledWalks
import OnlineSteinerForest.UpperBound.GirthSubdivisionChain

/-! An arbitrary nonbacktracking labelled walk gives a nonbacktracking standard walk. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem traceWalk_cons_first_edge (left right : I → V) {u v : V} (d : Dart I) (ds : List (Dart I))
    (h : TraceValid left right u v (d :: ds)) :
    (traceWalk left right (d :: ds) h).edges.head? =
      some s(.inl (tail left right d), .inr d) := by
  change (((dartWalk left right d).append (traceWalk left right ds h.2)).copy _ _).edges.head? = _
  rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_append, dartWalk_edges]
  rfl

theorem traceWalk_chain (left right : I → V) {u v : V} (ds : List (Dart I))
    (h : TraceValid left right u v ds) (hnb : TraceNonbacktracking ds) :
    List.IsChain (· ≠ ·) (traceWalk left right ds h).edges := by
  induction ds generalizing u with
  | nil => simp [traceWalk]
  | cons d ds ih =>
    change List.IsChain (· ≠ ·) (((dartWalk left right d).append
      (traceWalk left right ds h.2)).copy _ _).edges
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_append]
    have hnb' := List.isChain_cons.mp hnb
    apply (dartWalk_chain left right d).append (ih h.2 hnb'.2)
    intro a ha b hb
    simp only [dartWalk_edges, List.getLast?_cons_cons, List.getLast?_singleton,
      Option.mem_def, Option.some.injEq] at ha
    subst a
    cases ds with
    | nil => simpa [traceWalk] using hb
    | cons e es =>
      rw [traceWalk_cons_first_edge] at hb
      simp only [Option.mem_def, Option.some.injEq] at hb
      subst b
      have hne : e ≠ reverse d := hnb'.1 e (by simp)
      intro heq
      have hh : reverse d = e := by
        simp only [Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq, Sum.inr_ne_inl,
          Sum.inl_ne_inr, false_and, and_false, false_or] at heq
        exact heq.1
      exact hne hh.symm

end OnlineSteinerForest.UpperBound.Girth
