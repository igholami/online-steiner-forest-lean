import OnlineSteinerForest.LowerBound.Sampling.Balance

/-! Balancing two coordinates increases every elementary symmetric sum. -/
namespace OnlineSteinerForest.LowerBound.Sampling

variable {ι : Type*} [DecidableEq ι]

theorem elementary_balance_le (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    {a b : ι} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (mean : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (ham : w a ≤ mean) (hmb : mean ≤ w b) :
    elementary s r w ≤ elementary s r (balance w a b mean) := by
  rcases r with _ | (_ | r)
  · simp
  · change elementary s 1 w ≤ elementary s 1 (balance w a b mean)
    rw [elementary_one, elementary_one, balance_sum w s ha hb hab mean]
  · let rest := (s.erase a).erase b
    have heq : insert a (insert b rest) = s := insert_pair_erase s ha hb hab
    have han : a ∉ rest := by simp [rest]
    have hbn : b ∉ rest := by simp [rest]
    have herest (j : ℕ) : elementary rest j (balance w a b mean) = elementary rest j w :=
      elementary_congr rest j _ _ (balance_rest w s a b mean)
    have hc : 0 ≤ elementary rest r w := elementary_nonneg rest r w
      (fun i hi => hw i (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hi)))
    have hprod : w a * w b ≤ mean * (w a + w b - mean) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ham) (sub_nonneg.mpr hmb)]
    rw [← heq, elementary_insert_pair rest a b han hbn hab r,
      elementary_insert_pair rest a b han hbn hab r]
    rw [herest (r + 2), herest (r + 1), herest r,
      balance_left w hab, balance_right]
    nlinarith [mul_le_mul_of_nonneg_right hprod hc]

omit [DecidableEq ι] in
/-- A nonconstant vector with the specified mean has coordinates on both sides. -/
theorem exists_straddling (s : Finset ι) (w : ι → ℝ) (mean : ℝ)
    (hsum : ∑ i ∈ s, w i = s.card * mean)
    (hneq : ¬ ∀ i ∈ s, w i = mean) :
    (∃ a ∈ s, w a < mean) ∧ (∃ b ∈ s, mean < w b) := by
  constructor
  · by_contra h
    have hle : ∀ i ∈ s, mean ≤ w i :=
      fun i hi => le_of_not_gt (fun hlt => h ⟨i, hi, hlt⟩)
    have heq : ∑ _i ∈ s, mean = ∑ i ∈ s, w i := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using hsum.symm
    exact hneq (fun i hi => ((Finset.sum_eq_sum_iff_of_le hle).mp heq i hi).symm)
  · by_contra h
    have hle : ∀ i ∈ s, w i ≤ mean :=
      fun i hi => le_of_not_gt (fun hlt => h ⟨i, hi, hlt⟩)
    have heq : ∑ i ∈ s, w i = ∑ _i ∈ s, mean := by
      simpa only [Finset.sum_const, nsmul_eq_mul] using hsum
    exact hneq ((Finset.sum_eq_sum_iff_of_le hle).mp heq)

end OnlineSteinerForest.LowerBound.Sampling
