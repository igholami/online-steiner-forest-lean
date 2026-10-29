import OnlineSteinerForest.UpperBound.GirthSuppress

/-! Retraction of the suppressed vertex to the first surviving endpoint. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

def collapseVertex (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) (x : V) : SuppressedVertex v :=
  if hx : x = v then ⟨head left right d, (outgoing_pair_nonloop left right v d e hpair hlabels).1⟩
  else ⟨x, hx⟩

@[simp] theorem collapseVertex_self (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    (collapseVertex left right v d e hpair hlabels v).val = head left right d := by simp [collapseVertex]

@[simp] theorem collapseVertex_of_ne (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) (x : V) (hx : x ≠ v) :
    (collapseVertex left right v d e hpair hlabels x).val = x := by simp [collapseVertex, hx]

theorem outgoing_pair_tails (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) : tail left right d = v ∧ tail left right e = v := by
  constructor
  · have hm : d ∈ outgoing left right v := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2
  · have hm : e ∈ outgoing left right v := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2

end OnlineSteinerForest.UpperBound.Girth
