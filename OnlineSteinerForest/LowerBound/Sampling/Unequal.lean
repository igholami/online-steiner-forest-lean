import OnlineSteinerForest.LowerBound.Sampling.Balance

/-! Each balancing update strictly reduces the number of non-mean coordinates. -/
namespace OnlineSteinerForest.LowerBound.Sampling

variable {ι : Type*} [DecidableEq ι]

noncomputable def unequal (s : Finset ι) (w : ι → ℝ) (mean : ℝ) : Finset ι := by
  classical
  exact s.filter (fun i => w i ≠ mean)

omit [DecidableEq ι] in
@[simp] theorem mem_unequal (s : Finset ι) (w : ι → ℝ) (mean : ℝ) (i : ι) :
    i ∈ unequal s w mean ↔ i ∈ s ∧ w i ≠ mean := by
  classical
  simp [unequal]

theorem unequal_balance_card_lt (s : Finset ι) (w : ι → ℝ) {a b : ι}
    (ha : a ∈ s) (mean : ℝ) (ham : w a < mean) (hmb : mean < w b) :
    (unequal s (balance w a b mean) mean).card < (unequal s w mean).card := by
  classical
  have hab : a ≠ b := by intro h; subst b; linarith
  have hsub : unequal s (balance w a b mean) mean ⊆ (unequal s w mean).erase a := by
    intro i hi
    obtain ⟨his, hi⟩ := (mem_unequal _ _ _ _).mp hi
    have hia : i ≠ a := by intro h; subst i; exact hi (balance_left w hab mean)
    refine Finset.mem_erase.mpr ⟨hia, (mem_unequal _ _ _ _).mpr ⟨his, ?_⟩⟩
    by_cases hib : i = b
    · subst i
      exact ne_of_gt hmb
    · rwa [balance_other _ _ _ _ _ hia hib] at hi
  exact (Finset.card_le_card hsub).trans_lt
    (Finset.card_erase_lt_of_mem ((mem_unequal _ _ _ _).mpr ⟨ha, ne_of_lt ham⟩))

end OnlineSteinerForest.LowerBound.Sampling
