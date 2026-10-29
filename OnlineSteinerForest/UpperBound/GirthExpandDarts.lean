import OnlineSteinerForest.UpperBound.GirthLabelledWalks
import OnlineSteinerForest.UpperBound.GirthSuppress

/-! Expanding the merged edge into its two original labelled edges. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

def expandDart (d e : Dart I) : Dart (SuppressedEdge d e) → List (Dart I)
  | (none, false) => [reverse d, e]
  | (none, true) => [reverse e, d]
  | (some i, b) => [(i.val, b)]

def expandTrace (d e : Dart I) (ds : List (Dart (SuppressedEdge d e))) : List (Dart I) :=
  ds.flatMap (expandDart d e)

variable [Fintype I] [DecidableEq I]

theorem expandDart_cost (w : I → ℝ) (d e : Dart I) (a : Dart (SuppressedEdge d e)) :
    traceCost w (expandDart d e a) = suppressedWeight w d e a.1 := by
  rcases a with ⟨a, b⟩
  cases a with
  | none => cases b <;> simp [expandDart, traceCost, suppressedWeight, reverse, add_comm]
  | some i => simp [expandDart, traceCost, suppressedWeight]

theorem expandTrace_cost (w : I → ℝ) (d e : Dart I) (ds : List (Dart (SuppressedEdge d e))) :
    traceCost w (expandTrace d e ds) = traceCost (suppressedWeight w d e) ds := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    change traceCost w (expandDart d e a ++ expandTrace d e ds) = _
    simp only [traceCost, List.map_append, List.sum_append] at ih ⊢
    rw [show ((expandDart d e a).map fun a => w a.1).sum = suppressedWeight w d e a.1 from expandDart_cost w d e a, ih]
    rfl

end OnlineSteinerForest.UpperBound.Girth
