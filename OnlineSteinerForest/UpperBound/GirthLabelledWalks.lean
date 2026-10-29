import OnlineSteinerForest.UpperBound.GirthSubdivision

/-! Finite labelled walks used to transport cycles through degree-two suppression. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

def TraceValid (left right : I → V) : V → V → List (Dart I) → Prop
  | u, v, [] => u = v
  | u, v, d :: ds => tail left right d = u ∧ TraceValid left right (head left right d) v ds

attribute [reducible] TraceValid

abbrev TraceNonbacktracking (ds : List (Dart I)) : Prop :=
  List.IsChain (fun d e => e ≠ reverse d) ds

theorem traceValid_append (left right : I → V) {u v z : V} {ds es : List (Dart I)}
    (hds : TraceValid left right u v ds) (hes : TraceValid left right v z es) :
    TraceValid left right u z (ds ++ es) := by
  induction ds generalizing u with
  | nil => change u = v at hds; subst u; exact hes
  | cons d ds ih => exact ⟨hds.1, ih hds.2⟩

noncomputable def traceCost (w : I → ℝ) (ds : List (Dart I)) : ℝ := (ds.map fun d => w d.1).sum

variable [Fintype I] [DecidableEq I] [DecidableEq V]

def traceWalk (left right : I → V) : {u v : V} → (ds : List (Dart I)) →
    TraceValid left right u v ds → (edgeSubdivision left right).Walk (.inl u) (.inl v)
  | u, v, [], h => (.nil : (edgeSubdivision left right).Walk (.inl u) (.inl u)).copy rfl (congrArg Sum.inl h)
  | _, _, d :: ds, h =>
      ((dartWalk left right d).append (traceWalk left right ds h.2)).copy (congrArg Sum.inl h.1) rfl

end OnlineSteinerForest.UpperBound.Girth
