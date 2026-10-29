import OnlineSteinerForest.LowerBound.Probability.Patterns
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Separate the independent finite choices in the total raw-pattern weight. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

private def patternEquiv (h : ℕ) (i : Fin (matchingSize h)) (q : ℕ) :
    RawPattern h i q ≃
      (Fin (2 * matchingSize h) × (Fin q → Fin (2 * matchingSize h)) ×
       (Fin (q + 1) → (Fin (logSize h ^ 2) × Bool)) ×
       (Fin q ↪ {j : Fin (matchingSize h) // j ≠ i}) × (Fin q → Bool)) where
  toFun p := (p.start, p.destinations, p.runs, p.ranks, p.flip)
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_raw_pattern_weights (h : ℕ) (i : Fin (matchingSize h)) (q : ℕ) :
    (∑ p : RawPattern h i q, p.weight) =
      (2 * (matchingSize h : ℝ)) ^ (q + 1) * (2 : ℝ) ^ q *
        Real.exp (16 * rankFraction h i * rankPrice h i) *
        (∑ runs : Fin (q + 1) → (Fin (logSize h ^ 2) × Bool),
          ∏ j : Fin (q + 1), Real.exp (-(16 * rankFraction h i) *
            (((runs j).1.val + 1 : ℕ) : ℝ))) *
        ∑ ranks : Fin q ↪ {j : Fin (matchingSize h) // j ≠ i},
          ∏ j : Fin q, shortcutWeight h i (ranks j).val := by
  calc
    _ = ∑ x : (Fin (2 * matchingSize h) × (Fin q → Fin (2 * matchingSize h)) ×
        (Fin (q + 1) → (Fin (logSize h ^ 2) × Bool)) ×
        (Fin q ↪ {j : Fin (matchingSize h) // j ≠ i}) × (Fin q → Bool)),
        Real.exp (16 * rankFraction h i * rankPrice h i) *
          (∏ j : Fin (q + 1), Real.exp (-(16 * rankFraction h i) *
            (((x.2.2.1 j).1.val + 1 : ℕ) : ℝ))) *
          ∏ j : Fin q, shortcutWeight h i (x.2.2.2.1 j).val :=
      Fintype.sum_equiv (patternEquiv h i q) _ _ (fun _ => rfl)
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
        Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      simp only [pow_succ]
      ring

end OnlineSteinerForest.LowerBound.Probability
