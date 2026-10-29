import OnlineSteinerForest.UpperBound.GirthPruneLeaf
import OnlineSteinerForest.UpperBound.GirthCollision

/-! Collision witnesses lift through leaf deletion without changing their cost. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

def leafDartLift (d : Dart I) (a : Dart (PrunedLeafEdge d)) : Dart I := (a.1.val, a.2)

theorem leafDartLift_injective (d : Dart I) : Function.Injective (leafDartLift d) := by
  intro a b h
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  exact Prod.ext (Subtype.ext hf) hs

theorem leafTrace_valid (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) {x y : SuppressedVertex v}
    (ds : List (Dart (PrunedLeafEdge d))) (h : TraceValid (leafLeft left right v d hd)
      (leafRight left right v d hd) x y ds) :
    TraceValid left right x.val y.val (ds.map (leafDartLift d)) := by
  induction ds generalizing x with
  | nil => exact congrArg Subtype.val h
  | cons a ds ih =>
    constructor
    · have hh := congrArg Subtype.val h.1
      rcases a with ⟨a, b⟩
      cases b <;> exact hh
    · have hh := ih h.2
      rcases a with ⟨a, b⟩
      cases b <;> exact hh

theorem leafTrace_nonbacktracking (d : Dart I) (ds : List (Dart (PrunedLeafEdge d)))
    (h : TraceNonbacktracking ds) : TraceNonbacktracking (ds.map (leafDartLift d)) := by
  apply (List.isChain_map (leafDartLift d)).mpr
  apply h.imp
  intro a b hab heq
  apply hab
  apply leafDartLift_injective d
  exact heq

def liftLeafCollision (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d})
    (p : Collision (leafLeft left right v d hd) (leafRight left right v d hd)) : Collision left right where
  start := p.start.val
  finish := p.finish.val
  firstTrace := p.firstTrace.map (leafDartLift d)
  secondTrace := p.secondTrace.map (leafDartLift d)
  firstValid := leafTrace_valid left right v d hd p.firstTrace p.firstValid
  secondValid := leafTrace_valid left right v d hd p.secondTrace p.secondValid
  firstNonbacktracking := leafTrace_nonbacktracking d p.firstTrace p.firstNonbacktracking
  secondNonbacktracking := leafTrace_nonbacktracking d p.secondTrace p.secondNonbacktracking
  distinct := fun h => p.distinct ((List.map_injective_iff.mpr (leafDartLift_injective d)) h)

theorem liftLeafCollision_cost (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d})
    (p : Collision (leafLeft left right v d hd) (leafRight left right v d hd)) (w : I → ℝ) :
    (liftLeafCollision left right v d hd p).cost w = p.cost (fun i => w i.val) := by
  simp only [Collision.cost, liftLeafCollision, traceCost, List.map_map, Function.comp_def, leafDartLift]

end OnlineSteinerForest.UpperBound.Girth
