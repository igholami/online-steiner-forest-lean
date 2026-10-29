import OnlineSteinerForest.UpperBound.ZonesSubdivisionUniform

/-! Common-depth subdivision respects forest-component edge unions and disjointness. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
universe u
variable {V : Type u} [DecidableEq V]

@[simp] theorem subdivisionEdges_empty (n : ℕ) :
    subdivisionEdges (∅ : Finset (Sym2 V)) n = ∅ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [subdivisionEdges, ih]
    rfl

theorem subdivisionEdges_disjoint {E F : Finset (Sym2 V)} (hEF : Disjoint E F) (n : ℕ) :
    Disjoint (subdivisionEdges E n) (subdivisionEdges F n) := by
  induction n with
  | zero => exact hEF
  | succ n ih => exact zoneSplitUnion_disjoint ih

theorem subdivisionEdges_union (E F : Finset (Sym2 V)) (n : ℕ) :
    subdivisionEdges (E ∪ F) n = subdivisionEdges E n ∪ subdivisionEdges F n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [subdivisionEdges, ih]
    exact Finset.union_biUnion

theorem subdivisionEdges_biUnion {I : Type*} [DecidableEq I] (S : Finset I)
    (E : I → Finset (Sym2 V)) (n : ℕ) :
    subdivisionEdges (S.biUnion E) n = S.biUnion (fun i => subdivisionEdges (E i) n) := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.biUnion_insert, subdivisionEdges_union, ih, Finset.biUnion_insert]

end OnlineSteinerForest.UpperBound
