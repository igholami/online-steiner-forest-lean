import Mathlib.Data.Fin.Tuple.Basic
import Lean.Elab.Tactic.Omega

/-! Ordered slots for terminal endpoints and shortcut endpoints in a path pattern. -/
namespace OnlineSteinerForest.LowerBound.Probability

abbrev BoundarySlot (q : ℕ) := Fin 2 ⊕ (Fin q × Fin 2)

def boundarySlotIndex {q : ℕ} : BoundarySlot q → Fin (2 * q + 2)
  | .inl b => if b.val = 0 then ⟨0, by omega⟩ else ⟨2 * q + 1, by omega⟩
  | .inr (j, b) => ⟨2 * j.val + b.val + 1, by omega⟩

def boundarySlotOfIndex {q : ℕ} (n : Fin (2 * q + 2)) : BoundarySlot q :=
  if hzero : n.val = 0 then .inl 0
  else if hlast : n.val = 2 * q + 1 then .inl 1
  else .inr (⟨(n.val - 1) / 2, by omega⟩, ⟨(n.val - 1) % 2, by omega⟩)

theorem boundarySlotIndex_ofIndex {q : ℕ} (n : Fin (2 * q + 2)) :
    boundarySlotIndex (boundarySlotOfIndex n) = n := by
  unfold boundarySlotOfIndex
  split_ifs with hzero hlast
  · apply Fin.ext
    simp [boundarySlotIndex, hzero]
  · apply Fin.ext
    simp [boundarySlotIndex, hlast]
  · apply Fin.ext
    dsimp [boundarySlotIndex]
    omega

theorem boundarySlotOfIndex_index {q : ℕ} (s : BoundarySlot q) :
    boundarySlotOfIndex (boundarySlotIndex s) = s := by
  cases s with
  | inl b =>
    have hb : b.val = 0 ∨ b.val = 1 := by omega
    rcases hb with hb | hb
    · have hb' : b = 0 := Fin.ext hb
      subst b
      simp [boundarySlotIndex, boundarySlotOfIndex]
    · have hb' : b = 1 := Fin.ext hb
      subst b
      simp [boundarySlotIndex, boundarySlotOfIndex]
  | inr p =>
    rcases p with ⟨j, b⟩
    have hn0 : 2 * j.val + b.val + 1 ≠ 0 := by omega
    have hnlast : 2 * j.val + b.val + 1 ≠ 2 * q + 1 := by omega
    simp only [boundarySlotIndex, boundarySlotOfIndex, hn0, hnlast, ↓reduceDIte]
    congr 2 <;> apply Fin.ext <;> dsimp <;> omega

def boundarySlotEquiv (q : ℕ) : Fin (2 * q + 2) ≃ BoundarySlot q where
  toFun := boundarySlotOfIndex
  invFun := boundarySlotIndex
  left_inv := boundarySlotIndex_ofIndex
  right_inv := boundarySlotOfIndex_index

@[simp] theorem boundarySlotEquiv_zero (q : ℕ) :
    boundarySlotEquiv q 0 = .inl 0 := by simp [boundarySlotEquiv, boundarySlotOfIndex]

@[simp] theorem boundarySlotEquiv_last (q : ℕ) :
    boundarySlotEquiv q ⟨2 * q + 1, by omega⟩ = .inl 1 := by
  simp [boundarySlotEquiv, boundarySlotOfIndex]

end OnlineSteinerForest.LowerBound.Probability
