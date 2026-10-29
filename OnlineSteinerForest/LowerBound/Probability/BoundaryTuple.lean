import OnlineSteinerForest.LowerBound.Probability.BoundarySlots
import Mathlib.GroupTheory.Perm.Basic

/-! Injective domain tuples prescribing terminal and oriented shortcut endpoints. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable {m q : ℕ}

def orientSide (flip : Bool) : Equiv.Perm (Fin 2) :=
  if flip then Equiv.swap 0 1 else Equiv.refl _

def slotEmbedding : (Fin m × Fin 2) ↪ Fin (2 * m) where
  toFun p := ⟨2 * p.1.val + p.2.val, by omega⟩
  inj' p p' heq := by
    have he := congrArg Fin.val heq
    change 2 * p.1.val + p.2.val = 2 * p'.1.val + p'.2.val at he
    have hb := p.2.isLt
    have hb' := p'.2.isLt
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))

def boundaryRankEmbedding (i : Fin m) (ranks : Fin q ↪ {j : Fin m // j ≠ i})
    (flip : Fin q → Bool) : BoundarySlot q ↪ (Fin m × Fin 2) where
  toFun
    | .inl b => (i, b)
    | .inr (j, b) => ((ranks j).val, orientSide (flip j) b)
  inj' x y heq := by
    have hr := congrArg Prod.fst heq
    have hb := congrArg Prod.snd heq
    cases x with
    | inl b =>
      cases y with
      | inl c => exact congrArg Sum.inl hb
      | inr p =>
        rcases p with ⟨j, c⟩
        exact ((ranks j).prop hr.symm).elim
    | inr p =>
      rcases p with ⟨j, b⟩
      cases y with
      | inl c => exact ((ranks j).prop hr).elim
      | inr p' =>
        rcases p' with ⟨j', c⟩
        have hj : j = j' := ranks.injective (Subtype.ext hr)
        subst j'
        have hbc : b = c := (orientSide (flip j)).injective hb
        subst c
        rfl

/-- Its order is `[terminalLeft, shortcutStart₀, shortcutEnd₀, ..., terminalRight]`. -/
def boundaryTuple (i : Fin m) (ranks : Fin q ↪ {j : Fin m // j ≠ i}) (flip : Fin q → Bool) :
    Fin (2 * q + 2) ↪ Fin (2 * m) :=
  ((boundarySlotEquiv q).toEmbedding.trans (boundaryRankEmbedding i ranks flip)).trans slotEmbedding

@[simp] theorem boundaryTuple_zero (i : Fin m) (ranks : Fin q ↪ {j : Fin m // j ≠ i})
    (flip : Fin q → Bool) : boundaryTuple i ranks flip 0 = slotEmbedding (i, 0) := by
  change slotEmbedding (boundaryRankEmbedding i ranks flip (boundarySlotEquiv q 0)) = _
  rw [boundarySlotEquiv_zero]
  rfl

@[simp] theorem boundaryTuple_last (i : Fin m) (ranks : Fin q ↪ {j : Fin m // j ≠ i})
    (flip : Fin q → Bool) :
    boundaryTuple i ranks flip ⟨2 * q + 1, by omega⟩ = slotEmbedding (i, 1) := by
  change slotEmbedding (boundaryRankEmbedding i ranks flip
    (boundarySlotEquiv q ⟨2 * q + 1, by omega⟩)) = _
  rw [boundarySlotEquiv_last]
  rfl

@[simp] theorem boundaryTuple_shortcut (i : Fin m) (ranks : Fin q ↪ {j : Fin m // j ≠ i})
    (flip : Fin q → Bool) (j : Fin q) (b : Fin 2) :
    boundaryTuple i ranks flip (boundarySlotIndex (.inr (j, b))) =
      slotEmbedding ((ranks j).val, orientSide (flip j) b) := by
  change slotEmbedding (boundaryRankEmbedding i ranks flip
    (boundarySlotOfIndex (boundarySlotIndex (.inr (j, b))))) = _
  rw [boundarySlotOfIndex_index]
  rfl

end OnlineSteinerForest.LowerBound.Probability
