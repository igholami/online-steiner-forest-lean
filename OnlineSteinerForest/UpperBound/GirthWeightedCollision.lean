import OnlineSteinerForest.UpperBound.GirthMarkovBounds
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-! The finite weighted pigeonhole step in the short-cycle argument. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {P K : Type*} [Fintype P] [Fintype K]

/-- At least half the probability lies on outcomes of cost at most twice the mean bound. -/
theorem half_mass_below_double (μ cost : P → ℝ) (hμ : ∀ p, 0 ≤ μ p)
    (hcost : ∀ p, 0 ≤ cost p) (hnorm : ∑ p, μ p = 1) (B : ℝ) (hB : 0 < B)
    (hmean : ∑ p, μ p * cost p ≤ B) :
    1 / 2 ≤ ∑ p ∈ Finset.univ.filter (fun p => cost p ≤ 2 * B), μ p := by
  classical
  let good := Finset.univ.filter (fun p => cost p ≤ 2 * B)
  let bad := Finset.univ \ good
  have hpart : (∑ p ∈ good, μ p) + (∑ p ∈ bad, μ p) = 1 := by
    have hh := Finset.sum_add_sum_compl good μ
    have hb : bad = goodᶜ := by ext p; simp [bad]
    rw [hb, hh]
    exact hnorm
  have hbad : 2 * B * (∑ p ∈ bad, μ p) ≤ B := by
    calc
      _ = ∑ p ∈ bad, μ p * (2 * B) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ p ∈ bad, μ p * cost p := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' : ¬ cost p ≤ 2 * B := by simpa [bad, good] using hp
        exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hp')) (hμ p)
      _ ≤ ∑ p, μ p * cost p := Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (by intro p _ _; exact mul_nonneg (hμ p) (hcost p))
      _ ≤ B := hmean
  change 1 / 2 ≤ ∑ p ∈ good, μ p
  nlinarith

/-- Small atoms and sufficiently many good outcomes force two equal keys. -/
theorem weighted_key_collision (μ : P → ℝ) (S : Finset P) (key : P → K)
    (a : ℝ) (ha : 0 ≤ a) (hatom : ∀ p ∈ S, μ p ≤ a)
    (hmass : (Fintype.card K : ℝ) * a < ∑ p ∈ S, μ p) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ key p = key q := by
  classical
  by_contra hn
  have hinj : Set.InjOn key S := by
    intro p hp q hq he
    by_contra hne
    exact hn ⟨p, hp, q, hq, hne, he⟩
  have hcard : S.card ≤ Fintype.card K := by
    calc
      _ = (S.image key).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_univ _
  have hsum : (∑ p ∈ S, μ p) ≤ (Fintype.card K : ℝ) * a := by
    calc
      _ ≤ ∑ _p ∈ S, a := Finset.sum_le_sum hatom
      _ = (S.card : ℝ) * a := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) ha
  linarith

end OnlineSteinerForest.UpperBound.Girth
