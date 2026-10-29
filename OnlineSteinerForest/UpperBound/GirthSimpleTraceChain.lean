import OnlineSteinerForest.UpperBound.GirthSimpleTrace

/-! Nonbacktracking labelled traces stay nonbacktracking when distinct labels are simple edges. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] {G : SimpleGraph V}

theorem consecutive_label_edges_ne (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i))
    (hinj : Function.Injective (fun i => s(left i, right i))) (d e : Dart I)
    (hnext : tail left right e = head left right d) (hnb : e ≠ reverse d) :
    s(left d.1, right d.1) ≠ s(left e.1, right e.1) := by
  intro heq
  have hi := hinj heq
  rcases dart_eq_or_reverse_of_label_eq e d hi.symm with h | h
  · rw [h] at hnext
    exact (dart_adj left right ha d).ne hnext
  · exact hnb h

theorem simpleTraceWalk_chain (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i))
    (hinj : Function.Injective (fun i => s(left i, right i))) {u v : V}
    (ds : List (Dart I)) (h : TraceValid left right u v ds) (hnb : TraceNonbacktracking ds) :
    List.IsChain (· ≠ ·) (simpleTraceWalk left right ha ds h).edges := by
  rw [simpleTraceWalk_edges]
  induction ds generalizing u with
  | nil => simp
  | cons d ds ih =>
    cases ds with
    | nil => simp
    | cons e es =>
      have hn := List.isChain_cons_cons.mp hnb
      apply List.isChain_cons_cons.mpr
      exact ⟨consecutive_label_edges_ne left right ha hinj d e h.2.1 hn.1, ih h.2 hn.2⟩

theorem simpleTraceWalk_cost (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i))
    (c : Sym2 V → ℝ) {u v : V} (ds : List (Dart I)) (h : TraceValid left right u v ds) :
    ((simpleTraceWalk left right ha ds h).edges.map c).sum =
      traceCost (fun i => c s(left i, right i)) ds := by
  rw [simpleTraceWalk_edges, List.map_map]
  rfl

end OnlineSteinerForest.UpperBound.Girth
