import OnlineSteinerForest.UpperBound.GirthSuppress
import Mathlib.Data.Fintype.EquivFin

/-! The dart map for a degree-two suppression retains every other orientation. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {I : Type*} [Fintype I] [DecidableEq I]

def unsuppressDart (d e : Dart I) : Dart (SuppressedEdge d e) → Dart I
  | (none, false) => reverse d
  | (none, true) => reverse e
  | (some i, b) => (i.val, b)

theorem unsuppressDart_injective (d e : Dart I) (hlabels : d.1 ≠ e.1) :
    Function.Injective (unsuppressDart d e) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  cases a with
  | none =>
    cases a' with
    | none =>
      cases b <;> cases b' <;> simp_all [unsuppressDart, reverse, Prod.mk.injEq]
    | some i =>
      have hi₁ := i.property.1
      have hi₂ := i.property.2
      cases b <;> simp_all [unsuppressDart, reverse, Prod.mk.injEq]
  | some i =>
    cases a' with
    | none =>
      have hi₁ := i.property.1
      have hi₂ := i.property.2
      cases b' <;> simp_all [unsuppressDart, reverse, Prod.mk.injEq]
    | some j =>
      simp only [unsuppressDart, Prod.mk.injEq] at h
      exact Prod.ext (congrArg some (Subtype.ext h.1)) h.2

theorem unsuppressDart_avoids (d e : Dart I) (hlabels : d.1 ≠ e.1)
    (a : Dart (SuppressedEdge d e)) : unsuppressDart d e a ≠ d ∧ unsuppressDart d e a ≠ e := by
  rcases a with ⟨a, b⟩
  cases a with
  | none =>
    cases b
    · change reverse d ≠ d ∧ reverse d ≠ e
      refine ⟨reverse_ne_self d, ?_⟩
      intro h
      have hh := congrArg (fun x : Dart I => x.1) h
      exact hlabels hh
    · change reverse e ≠ d ∧ reverse e ≠ e
      refine ⟨?_, reverse_ne_self e⟩
      intro h
      have hh := congrArg (fun x : Dart I => x.1) h
      exact hlabels hh.symm
  | some i =>
    exact ⟨fun h => i.property.1 (congrArg Prod.fst h), fun h => i.property.2 (congrArg Prod.fst h)⟩

end OnlineSteinerForest.UpperBound.Girth
