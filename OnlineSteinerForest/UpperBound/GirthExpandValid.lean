import OnlineSteinerForest.UpperBound.GirthExpandDarts
import OnlineSteinerForest.UpperBound.GirthCollapseVertex

/-! Suppression expansion preserves the endpoints and validity of labelled walks. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem expandDart_valid (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (a : Dart (SuppressedEdge d e)) :
    TraceValid left right
      (tail (suppressedLeft left right v d e hpair hlabels) (suppressedRight left right v d e hpair hlabels) a).val
      (head (suppressedLeft left right v d e hpair hlabels) (suppressedRight left right v d e hpair hlabels) a).val
      (expandDart d e a) := by
  have ht := outgoing_pair_tails left right v d e hpair
  rcases a with ⟨a, b⟩
  cases a with
  | none =>
    cases b
    · exact ⟨tail_reverse left right d, ht.2.trans (ht.1.symm.trans (head_reverse left right d).symm), rfl⟩
    · exact ⟨tail_reverse left right e, ht.1.trans (ht.2.symm.trans (head_reverse left right e).symm), rfl⟩
  | some i => cases b <;> exact ⟨rfl, rfl⟩

theorem expandTrace_valid (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    {x y : SuppressedVertex v} (ds : List (Dart (SuppressedEdge d e)))
    (h : TraceValid (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels) x y ds) :
    TraceValid left right x.val y.val (expandTrace d e ds) := by
  induction ds generalizing x with
  | nil => exact congrArg Subtype.val h
  | cons a ds ih =>
    change TraceValid left right x.val y.val (expandDart d e a ++ expandTrace d e ds)
    rw [← h.1]
    exact traceValid_append left right (expandDart_valid left right v d e hpair hlabels a) (ih h.2)

end OnlineSteinerForest.UpperBound.Girth
