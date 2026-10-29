import OnlineSteinerForest.UpperBound.GirthSuppressionCollapse

/-! Degree-two suppression preserves connectedness of endpoint graphs. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem suppressed_endpoint_connected (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (hc : (endpointGraph left right).Connected) :
    (endpointGraph (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels)).Connected where
  preconnected x y := by
    have hh := reachable_map_of_adj_reachable (collapseVertex left right v d e hpair hlabels)
      (collapse_endpoint_adj left right v d e hpair hlabels) (hc.preconnected x.val y.val)
    convert hh using 1 <;> apply Subtype.ext
    · exact (collapseVertex_of_ne left right v d e hpair hlabels x.val x.property).symm
    · exact (collapseVertex_of_ne left right v d e hpair hlabels y.val y.property).symm
  nonempty := ⟨⟨head left right d, (outgoing_pair_nonloop left right v d e hpair hlabels).1⟩⟩

end OnlineSteinerForest.UpperBound.Girth
