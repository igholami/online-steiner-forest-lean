import OnlineSteinerForest.UpperBound.GirthSubdivision
import Mathlib.SetTheory.Cardinal.Finite

/-! Connected components of the simple subdivision, and labelled graph cycle rank. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I]

noncomputable def componentCount (left right : I → V) : ℕ :=
  Nat.card (edgeSubdivision left right).ConnectedComponent

noncomputable def cycleRank (left right : I → V) : ℕ :=
  Fintype.card I + componentCount left right - Fintype.card V

theorem componentCount_le_vertices (left right : I → V) :
    componentCount left right ≤ Fintype.card V := by
  have hsurj : Function.Surjective (fun v : V =>
      (edgeSubdivision left right).connectedComponentMk (.inl v)) := by
    intro C
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h a =>
      cases a with
      | inl v => exact ⟨v, rfl⟩
      | inr d =>
        refine ⟨tail left right d, ?_⟩
        exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (show (edgeSubdivision left right).Adj (.inl (tail left right d)) (.inr d) from rfl)
  simpa [componentCount, Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective _ hsurj

end OnlineSteinerForest.UpperBound.Girth
