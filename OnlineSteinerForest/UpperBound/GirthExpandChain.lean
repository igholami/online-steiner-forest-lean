import OnlineSteinerForest.UpperBound.GirthExpandDarts

/-! Two-edge expansion preserves nonbacktracking, including at block boundaries. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem expandDart_chain (d e : Dart I) (hlabels : d.1 ≠ e.1)
    (a : Dart (SuppressedEdge d e)) : TraceNonbacktracking (expandDart d e a) := by
  have hde : d ≠ e := fun h => hlabels (congrArg Prod.fst h)
  rcases a with ⟨a, b⟩
  cases a with
  | none => cases b <;> simp [expandDart, TraceNonbacktracking, hde, hde.symm]
  | some i => simp [expandDart, TraceNonbacktracking]

theorem expandDart_boundary (d e : Dart I) (hlabels : d.1 ≠ e.1)
    (a b : Dart (SuppressedEdge d e)) (hne : b ≠ reverse a) :
    ∀ x ∈ (expandDart d e a).getLast?, ∀ y ∈ (expandDart d e b).head?, y ≠ reverse x := by
  have hlabels_symm := hlabels.symm
  rcases a with ⟨a, c⟩
  rcases b with ⟨b, c'⟩
  cases a with
  | none =>
    cases b with
    | none =>
      cases c <;> cases c' <;> simp_all [expandDart, reverse, Prod.mk.injEq]
    | some j =>
      have hj₁ := j.property.1
      have hj₂ := j.property.2
      cases c <;> cases c' <;> simp_all [expandDart, reverse, Prod.mk.injEq]
  | some i =>
    have hi₁ := i.property.1
    have hi₂ := i.property.2
    have hi₁symm := hi₁.symm
    have hi₂symm := hi₂.symm
    cases b with
    | none => cases c <;> cases c' <;> simp_all [expandDart, reverse, Prod.mk.injEq]
    | some j =>
      cases c <;> cases c' <;> simp_all [expandDart, reverse, Prod.mk.injEq, Subtype.ext_iff]

theorem expandTrace_chain (d e : Dart I) (hlabels : d.1 ≠ e.1)
    (ds : List (Dart (SuppressedEdge d e))) (hnb : TraceNonbacktracking ds) :
    TraceNonbacktracking (expandTrace d e ds) := by
  have hn : [] ∉ ds.map (expandDart d e) := by
    intro h
    obtain ⟨a, _, ha⟩ := List.mem_map.mp h
    rcases a with ⟨a, b⟩
    cases a <;> cases b <;> simp [expandDart] at ha
  change List.IsChain (fun d e => e ≠ reverse d) (ds.flatMap (expandDart d e))
  have heq : ∀ xs : List (Dart (SuppressedEdge d e)), (xs.map (expandDart d e)).flatten = xs.flatMap (expandDart d e) := by
    intro xs
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  rw [← heq ds]
  apply (List.isChain_flatten hn).mpr
  constructor
  · intro xs hxs
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hxs
    exact expandDart_chain d e hlabels a
  · apply (List.isChain_map (expandDart d e)).mpr
    exact hnb.imp (fun a b hab => expandDart_boundary d e hlabels a b hab)

end OnlineSteinerForest.UpperBound.Girth
