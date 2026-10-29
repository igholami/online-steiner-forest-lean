import OnlineSteinerForest.LowerBound.Tests
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.Linarith

/-! The exact finite good/bad price partition and the averaging existence step. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

noncomputable def positiveRanks (h : ℕ) : Finset (Fin (matchingSize h)) := by
  classical
  exact Finset.univ.filter (fun i => firstRank h ≤ i.val + 1)

noncomputable def badRanks (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    Finset (Fin (matchingSize h)) := by
  classical
  exact (positiveRanks h).filter (fun i => ¬ GoodRank h σ i)

noncomputable def badPrice (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) : ℝ :=
  ∑ i ∈ badRanks h σ, rankPrice h i

theorem retainedRanks_eq_filter (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    retainedRanks h σ = (positiveRanks h).filter (GoodRank h σ) := by
  classical
  ext i
  simp [retainedRanks, positiveRanks]

theorem totalPrice_eq_positive (h : ℕ) : totalPrice h = ∑ i ∈ positiveRanks h, rankPrice h i := by
  classical
  unfold totalPrice positiveRanks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with hi
  · rfl
  · simp [rankPrice, price_of_lt h (i.val + 1) (Nat.lt_of_not_ge hi)]

theorem retained_add_bad_price (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    (∑ i ∈ retainedRanks h σ, rankPrice h i) + badPrice h σ = totalPrice h := by
  classical
  rw [retainedRanks_eq_filter, badPrice, badRanks,
    Finset.sum_filter_add_sum_filter_not]
  exact (totalPrice_eq_positive h).symm

theorem retainsHalf_iff_badPrice_le (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    RetainsHalf h σ ↔ badPrice h σ ≤ totalPrice h / 2 := by
  have ht := retained_add_bad_price h σ
  unfold RetainsHalf
  constructor <;> intro hh <;> linarith

/-- Finite averaging supplies a suitable matching once the mean discarded price is bounded.
This lemma does not assume the existence of such a matching. -/
theorem exists_retainsHalf_of_mean_bad (h : ℕ)
    (hmean : (∑ σ : Equiv.Perm (Fin (2 * matchingSize h)), badPrice h σ) ≤
      Fintype.card (Equiv.Perm (Fin (2 * matchingSize h))) * (totalPrice h / 2)) :
    ∃ σ : Equiv.Perm (Fin (2 * matchingSize h)), RetainsHalf h σ := by
  classical
  by_contra hn
  have hall (σ : Equiv.Perm (Fin (2 * matchingSize h))) : totalPrice h / 2 < badPrice h σ := by
    apply lt_of_not_ge
    intro hb
    exact hn ⟨σ, (retainsHalf_iff_badPrice_le h σ).mpr hb⟩
  have hstrict := Finset.sum_lt_sum (fun σ (_ : σ ∈ Finset.univ) => (hall σ).le)
    ⟨Equiv.refl _, Finset.mem_univ _, hall (Equiv.refl _)⟩
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hstrict
  linarith

end OnlineSteinerForest.LowerBound
