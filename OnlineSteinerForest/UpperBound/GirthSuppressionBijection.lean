import OnlineSteinerForest.UpperBound.GirthSuppressionDarts

/-! Suppression gives a bijection between surviving dart orientations. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem dart_eq_or_reverse_of_label_eq (a b : Dart I) (h : a.1 = b.1) : a = b ∨ a = reverse b := by
  rcases a with ⟨i, c⟩
  rcases b with ⟨j, d⟩
  change i = j at h
  subst j
  cases c <;> cases d <;> simp [reverse]

theorem unsuppressDart_surjective_away (d e : Dart I) (a : Dart I) (hd : a ≠ d) (he : a ≠ e) :
    ∃ b : Dart (SuppressedEdge d e), unsuppressDart d e b = a := by
  by_cases hlabeld : a.1 = d.1
  · have ha := (dart_eq_or_reverse_of_label_eq a d hlabeld).resolve_left hd
    exact ⟨(none, false), ha.symm⟩
  · by_cases hlabele : a.1 = e.1
    · have ha := (dart_eq_or_reverse_of_label_eq a e hlabele).resolve_left he
      exact ⟨(none, true), ha.symm⟩
    · exact ⟨(some ⟨a.1, hlabeld, hlabele⟩, a.2), Prod.eta a⟩

noncomputable def suppressionDartEquiv (d e : Dart I) (hlabels : d.1 ≠ e.1) :
    Dart (SuppressedEdge d e) ≃ {a : Dart I // a ≠ d ∧ a ≠ e} :=
  Equiv.ofBijective (fun a => ⟨unsuppressDart d e a, unsuppressDart_avoids d e hlabels a⟩) ⟨
    by intro a b h; exact unsuppressDart_injective d e hlabels (congrArg Subtype.val h),
    by
      intro a
      obtain ⟨b, hb⟩ := unsuppressDart_surjective_away d e a.val a.property.1 a.property.2
      exact ⟨b, Subtype.ext hb⟩⟩

end OnlineSteinerForest.UpperBound.Girth
