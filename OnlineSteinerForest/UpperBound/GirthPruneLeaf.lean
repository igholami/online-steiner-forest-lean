import OnlineSteinerForest.UpperBound.GirthDegreeTwo
import OnlineSteinerForest.UpperBound.GirthSuppress

/-! Concrete deletion of a leaf and its unique incident edge label. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem degree_one_outgoing (left right : I → V) (v : V) (hv : degree left right v = 1) :
    ∃ d : Dart I, outgoing left right v = {d} := Finset.card_eq_one.mp hv

theorem leaf_nonloop (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) : head left right d ≠ v := by
  intro hh
  have hr : reverse d ∈ outgoing left right v := by
    simp only [outgoing, Finset.mem_filter, Finset.mem_univ, true_and, tail_reverse]
    exact hh
  rw [hd] at hr
  exact reverse_ne_self d (Finset.mem_singleton.mp hr)

theorem leaf_edge_avoids (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) (i : I) (hi : i ≠ d.1) : left i ≠ v ∧ right i ≠ v := by
  have hh : ∀ b : Bool, tail left right (i, b) ≠ v := by
    intro b hb
    have hm : (i, b) ∈ outgoing left right v := by simp [outgoing, hb]
    rw [hd] at hm
    exact hi (congrArg Prod.fst (Finset.mem_singleton.mp hm))
  exact ⟨hh false, hh true⟩

abbrev PrunedLeafEdge (d : Dart I) := {i : I // i ≠ d.1}

def leafLeft (left right : I → V) (v : V) (d : Dart I) (hd : outgoing left right v = {d}) :
    PrunedLeafEdge d → SuppressedVertex v :=
  fun i => ⟨left i, (leaf_edge_avoids left right v d hd i i.property).1⟩

def leafRight (left right : I → V) (v : V) (d : Dart I) (hd : outgoing left right v = {d}) :
    PrunedLeafEdge d → SuppressedVertex v :=
  fun i => ⟨right i, (leaf_edge_avoids left right v d hd i i.property).2⟩

def leafCollapse (left right : I → V) (v : V) (d : Dart I)
    (hd : outgoing left right v = {d}) (x : V) : SuppressedVertex v :=
  if hx : x = v then ⟨head left right d, leaf_nonloop left right v d hd⟩ else ⟨x, hx⟩

theorem prunedLeafEdge_card (d : Dart I) : Fintype.card (PrunedLeafEdge d) + 1 = Fintype.card I := by
  have hh : Fintype.card (PrunedLeafEdge d) = Fintype.card I - 1 := by
    simp [PrunedLeafEdge, Fintype.card_subtype_compl]
  have hm : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨d.1⟩
  omega

end OnlineSteinerForest.UpperBound.Girth
