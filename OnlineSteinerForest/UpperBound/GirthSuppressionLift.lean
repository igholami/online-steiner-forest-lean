import OnlineSteinerForest.UpperBound.GirthCollapseVertex
import OnlineSteinerForest.UpperBound.GirthEndpointGraph

/-! Every edge after suppression lifts to an original endpoint walk. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem suppressed_dart_reachable (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (a : Dart (SuppressedEdge d e)) :
    (endpointGraph left right).Reachable
      (tail (suppressedLeft left right v d e hpair hlabels)
        (suppressedRight left right v d e hpair hlabels) a).val
      (head (suppressedLeft left right v d e hpair hlabels)
        (suppressedRight left right v d e hpair hlabels) a).val := by
  have ht := outgoing_pair_tails left right v d e hpair
  have hjoin : (endpointGraph left right).Reachable (head left right d) (head left right e) := by
    have hd := (dart_endpoint_reachable left right d).symm
    have he := dart_endpoint_reachable left right e
    rw [ht.1] at hd
    rw [ht.2] at he
    exact hd.trans he
  rcases a with ⟨a, b⟩
  cases a with
  | none => cases b; exact hjoin; exact hjoin.symm
  | some i =>
    cases b
    · exact dart_endpoint_reachable left right (i.val, false)
    · exact dart_endpoint_reachable left right (i.val, true)

theorem suppressed_endpoint_inclusion_adj (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (x y : SuppressedVertex v)
    (h : (endpointGraph (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels)).Adj x y) :
    (endpointGraph left right).Reachable x.val y.val := by
  obtain ⟨_, a, rfl, rfl⟩ := h
  exact suppressed_dart_reachable left right v d e hpair hlabels a

end OnlineSteinerForest.UpperBound.Girth
