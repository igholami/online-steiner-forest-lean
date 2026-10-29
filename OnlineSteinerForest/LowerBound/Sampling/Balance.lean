import OnlineSteinerForest.LowerBound.Sampling.Elementary
import Mathlib.Tactic.Linarith

/-! A sum-preserving update setting one coordinate to the population mean. -/
namespace OnlineSteinerForest.LowerBound.Sampling

variable {ι : Type*} [DecidableEq ι]

/-- Set `a` to the mean and adjust `b` to keep their sum unchanged. -/
noncomputable def balance (w : ι → ℝ) (a b : ι) (mean : ℝ) : ι → ℝ :=
  Function.update (Function.update w a mean) b (w a + w b - mean)

@[simp] theorem balance_left (w : ι → ℝ) {a b : ι} (hab : a ≠ b) (mean : ℝ) :
    balance w a b mean a = mean := by simp [balance, hab]

@[simp] theorem balance_right (w : ι → ℝ) (a b : ι) (mean : ℝ) :
    balance w a b mean b = w a + w b - mean := by simp [balance]

theorem balance_other (w : ι → ℝ) (a b i : ι) (mean : ℝ)
    (hia : i ≠ a) (hib : i ≠ b) : balance w a b mean i = w i := by
  simp [balance, hia, hib]

theorem insert_pair_erase (s : Finset ι) {a b : ι} (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) : insert a (insert b ((s.erase a).erase b)) = s := by
  rw [Finset.insert_erase (by simp [hb, hab.symm]), Finset.insert_erase ha]

theorem balance_rest (w : ι → ℝ) (s : Finset ι) (a b : ι) (mean : ℝ) :
    ∀ i ∈ (s.erase a).erase b, balance w a b mean i = w i := by
  intro i hi
  exact balance_other w a b i mean (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    (Finset.mem_erase.mp hi).1

theorem balance_sum (w : ι → ℝ) (s : Finset ι) {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (mean : ℝ) :
    ∑ i ∈ s, balance w a b mean i = ∑ i ∈ s, w i := by
  have heq := insert_pair_erase s ha hb hab
  have han : a ∉ insert b ((s.erase a).erase b) := by simp [hab]
  have hbn : b ∉ (s.erase a).erase b := Finset.notMem_erase _ _
  conv_lhs => rw [← heq, Finset.sum_insert han, Finset.sum_insert hbn]
  conv_rhs => rw [← heq, Finset.sum_insert han, Finset.sum_insert hbn]
  rw [balance_left w hab, balance_right,
    Finset.sum_congr rfl (balance_rest w s a b mean)]
  ring

theorem balance_nonneg (w : ι → ℝ) (s : Finset ι) {a b : ι} (mean : ℝ)
    (ha : a ∈ s) (hw : ∀ i ∈ s, 0 ≤ w i) (hmean : 0 ≤ mean) (hmb : mean ≤ w b) :
    ∀ i ∈ s, 0 ≤ balance w a b mean i := by
  intro i hi
  by_cases hib : i = b
  · subst i
    rw [balance_right]
    linarith [hw a ha]
  · by_cases hia : i = a
    · subst i
      simpa [balance, hib] using hmean
    · rw [balance_other _ _ _ _ _ hia hib]
      exact hw i hi

end OnlineSteinerForest.LowerBound.Sampling
