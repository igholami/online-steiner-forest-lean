import OnlineSteinerForest.UpperBound.GirthSuppressionCollapse
import OnlineSteinerForest.UpperBound.GirthComponents

/-! Degree-two suppression preserves standard connected components and cycle rank. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

noncomputable def endpointSuppressionComponentEquiv (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    (endpointGraph left right).ConnectedComponent ≃
      (endpointGraph (suppressedLeft left right v d e hpair hlabels)
        (suppressedRight left right v d e hpair hlabels)).ConnectedComponent :=
  componentEquivOfRetractions (collapseVertex left right v d e hpair hlabels) Subtype.val
    (collapse_endpoint_adj left right v d e hpair hlabels)
    (suppressed_endpoint_inclusion_adj left right v d e hpair hlabels)
    (by
      intro x
      by_cases hx : x = v
      · subst x
        have ht := (outgoing_pair_tails left right v d e hpair).1
        simpa only [collapseVertex_self, ht] using (dart_endpoint_reachable left right d).symm
      · simpa only [collapseVertex_of_ne left right v d e hpair hlabels x hx] using
          (SimpleGraph.Reachable.refl x : (endpointGraph left right).Reachable x x))
    (by
      intro x
      have heq : collapseVertex left right v d e hpair hlabels x.val = x :=
        Subtype.ext (collapseVertex_of_ne left right v d e hpair hlabels x.val x.property)
      rw [heq])

theorem suppressed_componentCount (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    componentCount (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels) = componentCount left right := by
  apply Nat.card_congr
  exact (endpointComponentEquiv _ _).trans
    ((endpointSuppressionComponentEquiv left right v d e hpair hlabels).symm.trans
      (endpointComponentEquiv left right).symm)

theorem suppressed_cycleRank (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    cycleRank (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels) = cycleRank left right := by
  have hv := suppressedVertex_card v
  have he := suppressedEdge_card d e hlabels
  have hc := suppressed_componentCount left right v d e hpair hlabels
  unfold cycleRank
  rw [hc]
  omega

end OnlineSteinerForest.UpperBound.Girth
