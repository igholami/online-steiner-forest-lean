import OnlineSteinerForest.LowerBound.Sampling.Smoothing
import OnlineSteinerForest.LowerBound.Sampling.Unequal

/-! The elementary symmetric mean inequality, proved by finite coordinate balancing. -/
namespace OnlineSteinerForest.LowerBound.Sampling

variable {ι : Type*} [DecidableEq ι]

/-- At fixed nonnegative sum, equal coordinates maximize every elementary symmetric sum. -/
theorem elementary_le_constant (s : Finset ι) (r : ℕ) (mean : ℝ) (hmean : 0 ≤ mean)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hsum : ∑ i ∈ s, w i = s.card * mean) :
    elementary s r w ≤ s.card.choose r * mean ^ r := by
  classical
  have haux : ∀ n : ℕ, ∀ w : ι → ℝ, (∀ i ∈ s, 0 ≤ w i) →
      (∑ i ∈ s, w i = s.card * mean) → (unequal s w mean).card = n →
      elementary s r w ≤ s.card.choose r * mean ^ r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw hsum hn
      by_cases heq : ∀ i ∈ s, w i = mean
      · rw [elementary_congr s r w (fun _ => mean) heq, elementary_constant]
      obtain ⟨⟨a, ha, ham⟩, ⟨b, hb, hmb⟩⟩ := exists_straddling s w mean hsum heq
      have hab : a ≠ b := by intro h; subst b; linarith
      have hz : ∀ i ∈ s, 0 ≤ balance w a b mean i :=
        balance_nonneg w s mean ha hw hmean hmb.le
      have hsumz : ∑ i ∈ s, balance w a b mean i = s.card * mean :=
        (balance_sum w s ha hb hab mean).trans hsum
      have hlt : (unequal s (balance w a b mean) mean).card < n := by
        rw [← hn]
        exact unequal_balance_card_lt s w ha mean ham hmb
      exact (elementary_balance_le s r w ha hb hab mean hw ham.le hmb.le).trans
        (ih _ hlt _ hz hsumz rfl)
  exact haux _ w hw hsum rfl

/-- Unnormalized form of the sampling bound, valid also for an empty sample. -/
theorem elementary_le_mean (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : s.Nonempty) :
    elementary s r w ≤ s.card.choose r * ((∑ i ∈ s, w i) / s.card) ^ r := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.card_pos.ne'
  apply elementary_le_constant s r _
    (div_nonneg (Finset.sum_nonneg hw) (Nat.cast_nonneg _)) w hw
  simpa only [mul_comm] using (div_mul_cancel₀ (∑ i ∈ s, w i) hcard).symm

/-- Lemma 5.1: the mean product of a uniform sample without replacement is
at most the corresponding power of the population mean. Subset sampling is
used here; order does not affect products. -/
theorem sampling_without_replacement (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : s.Nonempty) (hr : r ≤ s.card) :
    (∑ t ∈ s.powersetCard r, ∏ i ∈ t, w i) / s.card.choose r ≤
      ((∑ i ∈ s, w i) / s.card) ^ r := by
  have hchoose : (0 : ℝ) < s.card.choose r := Nat.cast_pos.mpr (Nat.choose_pos hr)
  apply (div_le_iff₀ hchoose).mpr
  simpa only [elementary, mul_comm] using elementary_le_mean s r w hw hs

end OnlineSteinerForest.LowerBound.Sampling
