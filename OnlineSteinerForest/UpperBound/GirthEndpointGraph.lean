import OnlineSteinerForest.UpperBound.GirthSubdivision
import OnlineSteinerForest.UpperBound.GirthComponentRetractions

/-! The usual simple graph on endpoints has the same components as the labelled subdivision. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

def endpointGraph (left right : I → V) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ d : Dart I, tail left right d = u ∧ head left right d = v
  symm.symm u v := by
    rintro ⟨hne, d, hd, he⟩
    exact ⟨hne.symm, reverse d, (tail_reverse left right d).trans he, (head_reverse left right d).trans hd⟩
  loopless.irrefl u := by rintro ⟨hne, _⟩; exact hne rfl

theorem dart_endpoint_reachable (left right : I → V) (d : Dart I) :
    (endpointGraph left right).Reachable (tail left right d) (head left right d) := by
  by_cases h : tail left right d = head left right d
  · rw [h]
  · exact SimpleGraph.Adj.reachable ⟨h, d, rfl, rfl⟩

def endpointProjection (left right : I → V) : (V ⊕ Dart I) → V
  | .inl v => v
  | .inr d => tail left right d

theorem endpointProjection_adj (left right : I → V) (a b : V ⊕ Dart I)
    (h : (edgeSubdivision left right).Adj a b) :
    (endpointGraph left right).Reachable (endpointProjection left right a) (endpointProjection left right b) := by
  cases a with
  | inl v =>
    cases b with
    | inl w => exact h.elim
    | inr d => change v = tail left right d at h; rw [h]; exact .refl _
  | inr d =>
    cases b with
    | inl v => change v = tail left right d at h; rw [h]; exact .refl _
    | inr e =>
      change e = reverse d at h
      subst e
      simpa [endpointProjection] using dart_endpoint_reachable left right d

theorem endpointInclusion_adj (left right : I → V) (u v : V) (h : (endpointGraph left right).Adj u v) :
    (edgeSubdivision left right).Reachable (.inl u) (.inl v) := by
  obtain ⟨_, d, rfl, rfl⟩ := h
  exact (dartWalk left right d).reachable

noncomputable def endpointComponentEquiv (left right : I → V) :
    (edgeSubdivision left right).ConnectedComponent ≃ (endpointGraph left right).ConnectedComponent :=
  componentEquivOfRetractions (endpointProjection left right) Sum.inl
    (endpointProjection_adj left right) (endpointInclusion_adj left right)
    (by
      intro a
      cases a with
      | inl v => exact .refl _
      | inr d => exact SimpleGraph.Adj.reachable (show (edgeSubdivision left right).Adj
          (.inl (tail left right d)) (.inr d) from rfl))
    (by intro v; exact .refl _)

end OnlineSteinerForest.UpperBound.Girth
