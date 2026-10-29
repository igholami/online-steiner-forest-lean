import OnlineSteinerForest.UpperBound.GirthLabelledWalks
import OnlineSteinerForest.UpperBound.GirthSuppressionBijection

/-! Interpreting labelled traces directly in a standard simple graph. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] {G : SimpleGraph V}

theorem dart_adj (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i)) (d : Dart I) :
    G.Adj (tail left right d) (head left right d) := by
  rcases d with ⟨i, b⟩
  cases b
  · exact ha i
  · exact (ha i).symm

theorem dart_edge_eq (left right : I → V) (d : Dart I) :
    s(tail left right d, head left right d) = s(left d.1, right d.1) := by
  rcases d with ⟨i, b⟩
  cases b
  · rfl
  · exact Sym2.eq_swap

def simpleTraceWalk (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i)) :
    {u v : V} → (ds : List (Dart I)) → TraceValid left right u v ds → G.Walk u v
  | u, _, [], h => (.nil : G.Walk u u).copy rfl h
  | _, _, d :: ds, h =>
      (SimpleGraph.Walk.cons (dart_adj left right ha d) (simpleTraceWalk left right ha ds h.2)).copy h.1 rfl

theorem simpleTraceWalk_edges (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i))
    {u v : V} (ds : List (Dart I)) (h : TraceValid left right u v ds) :
    (simpleTraceWalk left right ha ds h).edges = ds.map (fun d => s(left d.1, right d.1)) := by
  induction ds generalizing u with
  | nil => simp [simpleTraceWalk]
  | cons d ds ih =>
    change ((SimpleGraph.Walk.cons (dart_adj left right ha d)
      (simpleTraceWalk left right ha ds h.2)).copy _ _).edges = _
    rw [SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons, ih, dart_edge_eq]
    rfl

theorem dart_eq_of_edge_and_tail (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i))
    (hinj : Function.Injective (fun i => s(left i, right i))) (d e : Dart I)
    (hedge : s(left d.1, right d.1) = s(left e.1, right e.1))
    (htail : tail left right d = tail left right e) : d = e := by
  have hi := hinj hedge
  rcases dart_eq_or_reverse_of_label_eq e d hi.symm with h | h
  · exact h.symm
  · rw [h, tail_reverse] at htail
    exact ((dart_adj left right ha d).ne htail).elim

theorem simpleTrace_edge_lists_injective (left right : I → V) (ha : ∀ i, G.Adj (left i) (right i))
    (hinj : Function.Injective (fun i => s(left i, right i))) {u v : V}
    (ds es : List (Dart I)) (hd : TraceValid left right u v ds) (he : TraceValid left right u v es)
    (h : ds.map (fun d => s(left d.1, right d.1)) = es.map (fun d => s(left d.1, right d.1))) : ds = es := by
  induction ds generalizing u es with
  | nil => cases es <;> simpa using h
  | cons d ds ih =>
    cases es with
    | nil => simp at h
    | cons e es =>
      have hh := List.cons.inj h
      have hde := dart_eq_of_edge_and_tail left right ha hinj d e hh.1 (hd.1.trans he.1.symm)
      subst e
      exact congrArg (List.cons d) (ih es hd.2 he.2 hh.2)

end OnlineSteinerForest.UpperBound.Girth
