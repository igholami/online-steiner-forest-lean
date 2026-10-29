import OnlineSteinerForest.LowerBound.Sampling.MeanBound
import Mathlib.Data.Fintype.Perm

/-! Uniform ordered samples: each subset has exactly `r!` orders. -/
namespace OnlineSteinerForest.LowerBound.Sampling

variable {ι : Type*} [DecidableEq ι]

/-- A subset of size `r`, together with a bijective enumeration in sample order. -/
abbrev OrderedSample (s : Finset ι) (r : ℕ) :=
  Σ t : ↥(s.powersetCard r), Fin r ≃ ↥t.val

theorem card_orders (s : Finset ι) (r : ℕ) (t : ↥(s.powersetCard r)) :
    Fintype.card (Fin r ≃ ↥t.val) = r.factorial := by
  classical
  have ht : Fintype.card (Fin r) = Fintype.card ↥t.val := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Finset.mem_powersetCard.mp t.prop).2.symm
  simpa only [Fintype.card_fin] using Fintype.card_equiv (Fintype.equivOfCardEq ht)

theorem card_orderedSample (s : Finset ι) (r : ℕ) :
    Fintype.card (OrderedSample s r) = s.card.choose r * r.factorial := by
  classical
  rw [Fintype.card_sigma]
  simp_rw [card_orders]
  simp

omit [DecidableEq ι] in
theorem ordered_product_eq (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (t : ↥(s.powersetCard r)) (e : Fin r ≃ ↥t.val) :
    (∏ j : Fin r, w (e j).val) = ∏ i ∈ t.val, w i := by
  rw [e.prod_comp (fun i : ↥t.val => w i.val)]
  exact Finset.prod_coe_sort t.val w

theorem sum_ordered_products (s : Finset ι) (r : ℕ) (w : ι → ℝ) :
    (∑ q : OrderedSample s r, ∏ j : Fin r, w (q.2 j).val) =
      r.factorial * elementary s r w := by
  classical
  rw [Fintype.sum_sigma]
  simp only [ordered_product_eq, Finset.sum_const, nsmul_eq_mul, card_orders, Finset.card_univ]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort (s.powersetCard r) (fun t => ∏ i ∈ t, w i)

/-- The manuscript's sampling lemma with the uniform average written explicitly
as a finite sum over ordered samples without replacement. -/
theorem ordered_sampling_without_replacement (s : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hs : s.Nonempty) (hr : r ≤ s.card) :
    (∑ q : OrderedSample s r, ∏ j : Fin r, w (q.2 j).val) /
        Fintype.card (OrderedSample s r) ≤ ((∑ i ∈ s, w i) / s.card) ^ r := by
  classical
  rw [sum_ordered_products, card_orderedSample, Nat.cast_mul, mul_comm (s.card.choose r : ℝ)]
  rw [mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr (Nat.factorial_pos r).ne')]
  exact sampling_without_replacement s r w hw hs hr

end OnlineSteinerForest.LowerBound.Sampling
