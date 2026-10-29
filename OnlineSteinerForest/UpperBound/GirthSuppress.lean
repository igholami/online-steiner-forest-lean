import OnlineSteinerForest.UpperBound.GirthDegreeTwo
import OnlineSteinerForest.Graph.Cost
import Mathlib.Data.Fintype.Option

/-! Actual suppression of a degree-two vertex with two distinct edge labels. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

abbrev SuppressedVertex (v : V) := {x : V // x ≠ v}
abbrev SuppressedEdge (d e : Dart I) := Option {i : I // i ≠ d.1 ∧ i ≠ e.1}

def suppressedLeft (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    SuppressedEdge d e → SuppressedVertex v
  | none => ⟨head left right d, (outgoing_pair_nonloop left right v d e hpair hlabels).1⟩
  | some i => ⟨left i, (remaining_edge_avoids_vertex left right v d e hpair i i.property.1 i.property.2).1⟩

def suppressedRight (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    SuppressedEdge d e → SuppressedVertex v
  | none => ⟨head left right e, (outgoing_pair_nonloop left right v d e hpair hlabels).2⟩
  | some i => ⟨right i, (remaining_edge_avoids_vertex left right v d e hpair i i.property.1 i.property.2).2⟩

noncomputable def suppressedWeight (w : I → ℝ) (d e : Dart I) : SuppressedEdge d e → ℝ
  | none => w d.1 + w e.1
  | some i => w i

theorem suppressedWeight_nonneg (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) (d e : Dart I)
    (i : SuppressedEdge d e) : 0 ≤ suppressedWeight w d e i := by
  cases i with
  | none => exact add_nonneg (hw d.1) (hw e.1)
  | some i => exact hw i

theorem suppressedVertex_card (v : V) : Fintype.card (SuppressedVertex v) + 1 = Fintype.card V := by
  have hh : Fintype.card (SuppressedVertex v) = Fintype.card V - 1 := by
    simp [SuppressedVertex, Fintype.card_subtype_compl]
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  omega

theorem suppressedEdge_card (d e : Dart I) (hlabels : d.1 ≠ e.1) :
    Fintype.card (SuppressedEdge d e) + 1 = Fintype.card I := by
  have hfilter : (Finset.univ.filter (fun i : I => i ≠ d.1 ∧ i ≠ e.1)) = Finset.univ \ {d.1, e.1} := by
    ext i; simp
  have hh : Fintype.card {i : I // i ≠ d.1 ∧ i ≠ e.1} = Fintype.card I - 2 := by
    rw [Fintype.card_subtype, hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hlabels]
  have hm : 2 ≤ Fintype.card I := by
    have hp := Finset.card_le_univ ({d.1, e.1} : Finset I)
    simpa [hlabels] using hp
  simp only [SuppressedEdge, Fintype.card_option]
  omega

end OnlineSteinerForest.UpperBound.Girth
