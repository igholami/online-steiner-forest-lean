import OnlineSteinerForest.UpperBound.SparseCore
import Lean.Elab.Tactic.Omega

/-! Correctness and discarded-edge accounting for the actual sparse-core algorithm. -/
namespace OnlineSteinerForest.UpperBound

variable {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]

theorem liveEdges_erase (left right : I → V) (S : Finset V) (v : V) :
    liveEdges left right (S.erase v) = liveEdges left right S \ incidentEdges left right S v := by
  ext i
  constructor
  · intro hi
    obtain ⟨_, hl, hr, hne⟩ := Finset.mem_filter.mp hi
    have hleft := Finset.mem_erase.mp hl
    have hright := Finset.mem_erase.mp hr
    have hLive : i ∈ liveEdges left right S := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hleft.2, hright.2, hne⟩
    refine Finset.mem_sdiff.mpr ⟨hLive, ?_⟩
    intro hinc
    rcases (Finset.mem_filter.mp hinc).2 with he | he
    · exact hleft.1 he
    · exact hright.1 he
  · intro hi
    obtain ⟨hLive, hn⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨_, hl, hr, hne⟩ := Finset.mem_filter.mp hLive
    have hleft : left i ≠ v := fun he => hn (Finset.mem_filter.mpr ⟨hLive, Or.inl he⟩)
    have hright : right i ≠ v := fun he => hn (Finset.mem_filter.mpr ⟨hLive, Or.inr he⟩)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hleft, hl⟩,
      Finset.mem_erase.mpr ⟨hright, hr⟩, hne⟩

/-- Peeling preserves a subset, stops only at minimum degree `D`, and discards
at most `D` edges per deleted vertex. All degrees refer to the current live edges. -/
theorem sparseCore_spec (left right : I → V) (D : ℕ) (S : Finset V) :
    sparseCore left right D S ⊆ S ∧
      (∀ v ∈ sparseCore left right D S,
        D ≤ (incidentEdges left right (sparseCore left right D S) v).card) ∧
      (liveEdges left right S).card ≤ (liveEdges left right (sparseCore left right D S)).card +
        D * (S.card - (sparseCore left right D S).card) := by
  classical
  have aux : ∀ n : ℕ, ∀ S : Finset V, S.card = n →
      sparseCore left right D S ⊆ S ∧
        (∀ v ∈ sparseCore left right D S,
          D ≤ (incidentEdges left right (sparseCore left right D S) v).card) ∧
        (liveEdges left right S).card ≤ (liveEdges left right (sparseCore left right D S)).card +
          D * (S.card - (sparseCore left right D S).card) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hn
      by_cases hs : ∃ v ∈ S, (incidentEdges left right S v).card < D
      · have hv := Classical.choose_spec hs
        let v := Classical.choose hs
        have hvS : v ∈ S := hv.1
        have hvD : (incidentEdges left right S v).card < D := hv.2
        have hlt : (S.erase v).card < n := by
          rw [← hn]
          exact Finset.card_erase_lt_of_mem hvS
        obtain ⟨hsub, hdeg, hbudget⟩ := ih (S.erase v).card hlt (S.erase v) rfl
        rw [sparseCore, dite_eq_left hs]
        change sparseCore left right D (S.erase v) ⊆ S ∧ _
        refine ⟨hsub.trans (Finset.erase_subset _ _), hdeg, ?_⟩
        have hinc : incidentEdges left right S v ⊆ liveEdges left right S := Finset.filter_subset _ _
        have hincle := Finset.card_le_card hinc
        have herase : (liveEdges left right (S.erase v)).card =
            (liveEdges left right S).card - (incidentEdges left right S v).card := by
          rw [liveEdges_erase, Finset.card_sdiff_of_subset hinc]
        have hstep : (liveEdges left right S).card ≤ (liveEdges left right (S.erase v)).card + D := by
          omega
        have hcoresize := Finset.card_le_card hsub
        have hdiff : S.card - (sparseCore left right D (S.erase v)).card =
            ((S.erase v).card - (sparseCore left right D (S.erase v)).card) + 1 := by
          have hcard := Finset.card_erase_of_mem hvS
          omega
        rw [hdiff, Nat.mul_add, Nat.mul_one]
        dsimp only [v] at *
        omega
      · rw [sparseCore, dite_eq_right hs]
        refine ⟨Finset.Subset.refl _, ?_, ?_⟩
        · intro v hv
          exact Nat.le_of_not_gt (fun hd => hs ⟨v, hv, hd⟩)
        · simp
  exact aux S.card S rfl

end OnlineSteinerForest.UpperBound
