import OnlineSteinerForest.UpperBound.GirthLabelledWalks
import OnlineSteinerForest.UpperBound.GirthTrace

/-! Injective support encoding of arbitrary labelled walks in the simple subdivision. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem traceWalk_support (left right : I → V) {u v : V} (ds : List (Dart I))
    (h : TraceValid left right u v ds) :
    (traceWalk left right ds h).support = .inl u :: ds.flatMap (nodeTriple left right) := by
  induction ds generalizing u with
  | nil => simp [traceWalk]
  | cons d ds ih =>
    change (((dartWalk left right d).append (traceWalk left right ds h.2)).copy _ _).support = _
    rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_append, dartWalk_support, ih]
    change _ = .inl u :: (nodeTriple left right d ++ ds.flatMap (nodeTriple left right))
    rw [← h.1]
    rfl

theorem decode_flatMap_nodeTriple (left right : I → V) (ds : List (Dart I)) :
    decodeTrace (ds.flatMap (nodeTriple left right)) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simpa [nodeTriple, decodeTrace] using congrArg (List.cons d) ih

theorem traceWalk_support_injective (left right : I → V) {u v x y : V}
    (ds es : List (Dart I)) (hd : TraceValid left right u v ds) (he : TraceValid left right x y es)
    (h : (traceWalk left right ds hd).support = (traceWalk left right es he).support) : ds = es := by
  have hh := congrArg (fun xs => decodeTrace xs.tail) h
  simpa only [traceWalk_support, List.tail_cons, decode_flatMap_nodeTriple] using hh

end OnlineSteinerForest.UpperBound.Girth
