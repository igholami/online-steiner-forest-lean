import OnlineSteinerForest.UpperBound.GirthExpandDarts

/-! The two-edge expansion has an explicit left inverse, so parallel labels stay distinct. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {I : Type*} [Fintype I] [DecidableEq I]

def decodeExpansion (d e : Dart I) : List (Dart I) → List (Dart (SuppressedEdge d e))
  | [] => []
  | a :: ds =>
    if hd : a.1 = d.1 then (none, false) :: decodeExpansion d e ds.tail
    else if he : a.1 = e.1 then (none, true) :: decodeExpansion d e ds.tail
    else (some ⟨a.1, hd, he⟩, a.2) :: decodeExpansion d e ds
termination_by ds => ds.length
decreasing_by
  all_goals
    simp_wf

theorem decodeExpansion_prefix (d e : Dart I) (hlabels : d.1 ≠ e.1)
    (a : Dart (SuppressedEdge d e)) (ds : List (Dart I)) :
    decodeExpansion d e (expandDart d e a ++ ds) = a :: decodeExpansion d e ds := by
  rcases a with ⟨a, b⟩
  cases a with
  | none => cases b <;> simp [expandDart, decodeExpansion, reverse, hlabels, hlabels.symm]
  | some i =>
    have hi₁ := i.property.1
    have hi₂ := i.property.2
    simp [expandDart, decodeExpansion, hi₁, hi₂]

theorem decodeExpansion_expandTrace (d e : Dart I) (hlabels : d.1 ≠ e.1)
    (ds : List (Dart (SuppressedEdge d e))) : decodeExpansion d e (expandTrace d e ds) = ds := by
  induction ds with
  | nil => simp [expandTrace, decodeExpansion]
  | cons a ds ih =>
    change decodeExpansion d e (expandDart d e a ++ expandTrace d e ds) = _
    rw [decodeExpansion_prefix d e hlabels, ih]

theorem expandTrace_injective (d e : Dart I) (hlabels : d.1 ≠ e.1) :
    Function.Injective (expandTrace d e) := by
  intro ds es h
  have hh := congrArg (decodeExpansion d e) h
  simpa only [decodeExpansion_expandTrace d e hlabels] using hh

end OnlineSteinerForest.UpperBound.Girth
