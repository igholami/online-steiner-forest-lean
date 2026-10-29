import OnlineSteinerForest.UpperBound.ReplacementBernoulli

/-! Sample centers, then add every vertex whose closed neighborhood was missed. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def chosenVertices (x : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => x v = true)

noncomputable def missedVertices (N : V → Finset V) (x : V → Bool) : Finset V :=
  Finset.univ.filter (fun v => ∀ u ∈ N v, x u = false)

noncomputable def augmentedCenters (N : V → Finset V) (x : V → Bool) : Finset V :=
  chosenVertices x ∪ missedVertices N x

theorem augmentedCenters_hit (N : V → Finset V) (hN : ∀ v, v ∈ N v)
    (x : V → Bool) (v : V) : ∃ u ∈ augmentedCenters N x, u ∈ N v := by
  by_cases hm : ∀ u ∈ N v, x u = false
  · exact ⟨v, Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩), hN v⟩
  · obtain ⟨u, hu⟩ := Classical.not_forall.mp hm
    obtain ⟨hu, hxu⟩ := Classical.not_forall.mp hu
    have htrue : x u = true := by cases hh : x u <;> simp_all
    exact ⟨u, Finset.mem_union_left _ (by simp [chosenVertices, htrue]), hu⟩

omit [DecidableEq V] in
theorem cast_card_filter (P : V → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ) = ∑ v, if P v then (1 : ℝ) else 0 := by
  symm
  rw [← Finset.sum_filter]
  simp

theorem mean_chosen_card (p : ℝ) :
    (∑ x : V → Bool, bernoulliWeight p x * (chosenVertices x).card) = Fintype.card V * p := by
  simp only [chosenVertices, cast_card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hm (v : V) : (∑ x : V → Bool, bernoulliWeight p x *
      (if x v = true then 1 else 0)) = p := by
    simpa [coinWeight] using bernoulli_prescribed p {v} true
  simp_rw [hm]
  simp [nsmul_eq_mul]

theorem mean_missed_card (p : ℝ) (N : V → Finset V) :
    (∑ x : V → Bool, bernoulliWeight p x * (missedVertices N x).card) =
      ∑ v, (1 - p) ^ (N v).card := by
  simp only [missedVertices, cast_card_filter, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  simpa only [coinWeight, Bool.false_eq_true, ↓reduceIte] using
    bernoulli_prescribed p (N v) false

theorem mean_augmented_card_le (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (N : V → Finset V) :
    (∑ x : V → Bool, bernoulliWeight p x * (augmentedCenters N x).card) ≤
      Fintype.card V * p + ∑ v, (1 - p) ^ (N v).card := by
  calc
    _ ≤ ∑ x : V → Bool, bernoulliWeight p x *
        ((chosenVertices x).card + (missedVertices N x).card : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (bernoulliWeight_nonneg p hp hp' x)
      exact_mod_cast Finset.card_union_le (chosenVertices x) (missedVertices N x)
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [mean_chosen_card, mean_missed_card]

end OnlineSteinerForest.UpperBound
