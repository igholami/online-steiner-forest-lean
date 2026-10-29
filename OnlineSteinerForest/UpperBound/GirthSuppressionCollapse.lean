import OnlineSteinerForest.UpperBound.GirthSuppressionLift
import OnlineSteinerForest.UpperBound.GirthSuppressionBijection

/-! Original endpoint edges map to connecting walks after degree-two suppression. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem collapse_dart_reachable (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) (a : Dart I) :
    (endpointGraph (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels)).Reachable
      (collapseVertex left right v d e hpair hlabels (tail left right a))
      (collapseVertex left right v d e hpair hlabels (head left right a)) := by
  let f := collapseVertex left right v d e hpair hlabels
  let L := suppressedLeft left right v d e hpair hlabels
  let R := suppressedRight left right v d e hpair hlabels
  have ht := outgoing_pair_tails left right v d e hpair
  have hn := outgoing_pair_nonloop left right v d e hpair hlabels
  have hd : (endpointGraph L R).Reachable (f (tail left right d)) (f (head left right d)) := by
    have heq : f (tail left right d) = f (head left right d) := by
      apply Subtype.ext
      simp [f, ht.1, hn.1]
    rw [heq]
  have he : (endpointGraph L R).Reachable (f (tail left right e)) (f (head left right e)) := by
    have hh := dart_endpoint_reachable L R (none, false)
    convert hh using 1
    · apply Subtype.ext
      change (collapseVertex left right v d e hpair hlabels (tail left right e)).val = head left right d
      rw [ht.2, collapseVertex_self]
    · apply Subtype.ext
      exact collapseVertex_of_ne left right v d e hpair hlabels (head left right e) hn.2
  have hrev : ∀ b : Dart I, (endpointGraph L R).Reachable (f (tail left right b)) (f (head left right b)) →
      (endpointGraph L R).Reachable (f (tail left right (reverse b))) (f (head left right (reverse b))) := by
    intro b hb
    simpa only [tail_reverse, head_reverse] using hb.symm
  by_cases had : a.1 = d.1
  · rcases dart_eq_or_reverse_of_label_eq a d had with rfl | rfl
    · exact hd
    · exact hrev d hd
  · by_cases hae : a.1 = e.1
    · rcases dart_eq_or_reverse_of_label_eq a e hae with rfl | rfl
      · exact he
      · exact hrev e he
    · have havoid := remaining_edge_avoids_vertex left right v d e hpair a.1 had hae
      have hh := dart_endpoint_reachable L R (some ⟨a.1, had, hae⟩, a.2)
      convert hh using 1 <;> apply Subtype.ext <;>
        cases hb : a.2 <;> simp [f, L, R, collapseVertex, tail, head, suppressedLeft, suppressedRight, hb, havoid.1, havoid.2]

theorem collapse_endpoint_adj (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) (x y : V)
    (h : (endpointGraph left right).Adj x y) :
    (endpointGraph (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels)).Reachable
      (collapseVertex left right v d e hpair hlabels x) (collapseVertex left right v d e hpair hlabels y) := by
  obtain ⟨_, a, rfl, rfl⟩ := h
  exact collapse_dart_reachable left right v d e hpair hlabels a

end OnlineSteinerForest.UpperBound.Girth
