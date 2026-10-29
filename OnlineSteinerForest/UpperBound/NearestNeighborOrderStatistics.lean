import OnlineSteinerForest.UpperBound.NearestNeighborHarmonic
import Mathlib.Data.List.Sort
import Mathlib.Data.List.FinRange
import OnlineSteinerForest.Graph.Cost

/-! Threshold packing implies a logarithmic bound on the sum of insertion distances. -/
namespace OnlineSteinerForest.UpperBound

/-- The order-statistic argument in manuscript Lemma 4.4, with no graph assumptions hidden. -/
theorem sum_le_log_of_threshold_packing (n : ℕ) (a : Fin n → ℝ) (T : ℝ)
    (hT : 0 ≤ T) (ha : ∀ i, 0 ≤ a i)
    (hpack : ∀ (J : Finset (Fin n)), J.Nonempty → ∀ r : ℝ, 0 < r →
      (∀ i ∈ J, r ≤ a i) → ((J.card : ℝ) + 1) * r ≤ T) :
    (∑ i : Fin n, a i) ≤ T * Real.log ((n + 1 : ℕ) : ℝ) := by
  classical
  let cmp : Fin n → Fin n → Bool := fun i j => decide (a j ≤ a i)
  let xs := (List.finRange n).mergeSort cmp
  have hperm : xs.Perm (List.finRange n) := List.mergeSort_perm _ _
  have hlen : xs.length = n := by simpa using hperm.length_eq
  have hnodup : xs.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange n)
  have hsort : xs.Pairwise (fun i j => a j ≤ a i) := by
    have hs := List.pairwise_mergeSort (le := cmp)
      (fun i j k hij hjk => by
        simp only [cmp, decide_eq_true_eq] at hij hjk ⊢
        exact hjk.trans hij)
      (fun i j => by simp only [cmp, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
      (List.finRange n)
    simpa only [cmp, decide_eq_true_eq] using hs
  have hterm (k : Fin n) : a (xs[k.val]'(by rw [hlen]; exact k.isLt)) ≤ T / (k.val + 2) := by
    let b := xs[k.val]'(by rw [hlen]; exact k.isLt)
    by_cases hb : 0 < a b
    · let J := (xs.take (k.val + 1)).toFinset
      have hJcard : J.card = k.val + 1 := by
        rw [List.toFinset_card_of_nodup (hnodup.take (i := k.val + 1)), List.length_take, hlen, Nat.min_eq_left (by omega)]
      have hJnonempty : J.Nonempty := Finset.card_pos.mp (by rw [hJcard]; omega)
      have hJ : ∀ i ∈ J, a b ≤ a i := by
        intro i hi
        obtain ⟨j, hj, heq⟩ := List.mem_take_iff_getElem.mp (List.mem_toFinset.mp hi)
        have hjlen : j < xs.length := lt_of_lt_of_le hj (Nat.min_le_right _ _)
        have hjk : j ≤ k.val := by omega
        by_cases he : j = k.val
        · subst j
          exact le_of_eq (congrArg a heq)
        · have hh := (List.pairwise_iff_getElem.mp hsort) j k.val hjlen (by rw [hlen]; exact k.isLt) (by omega)
          simpa only [b, heq] using hh
      have hp := hpack J hJnonempty (a b) hb hJ
      rw [hJcard, Nat.cast_add, Nat.cast_one] at hp
      apply (le_div_iff₀ (show (0 : ℝ) < k.val + 2 by positivity)).mpr
      nlinarith
    · have hb0 : a b = 0 := le_antisymm (le_of_not_gt hb) (ha b)
      change a b ≤ _
      rw [hb0]
      exact div_nonneg hT (by positivity)
  have hsum : (∑ i : Fin n, a i) = ∑ k : Fin n, a (xs[k.val]'(by rw [hlen]; exact k.isLt)) := by
    have hx : (xs.map a).sum = ((List.finRange n).map a).sum := hperm.map a |>.sum_eq
    have hget := List.sum_ofFn (f := fun k : Fin n => a (xs[k.val]'(by rw [hlen]; exact k.isLt)))
    have hmap : List.ofFn (fun k : Fin n => a (xs[k.val]'(by rw [hlen]; exact k.isLt))) = xs.map a := by
      apply List.ext_getElem
      · simp [hlen]
      · intro i hi hj
        simp
    rw [hmap, hx] at hget
    simpa only [Fin.sum_ofFn, ← List.ofFn_eq_map] using hget
  calc
    _ = _ := hsum
    _ ≤ ∑ k : Fin n, T / (k.val + 2) := Finset.sum_le_sum (fun k _ => hterm k)
    _ = T * ∑ k ∈ Finset.range n, (((k + 2 : ℕ) : ℝ)⁻¹) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => T / ((k : ℝ) + 2)) n, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp [div_eq_mul_inv]
    _ ≤ _ := mul_le_mul_of_nonneg_left (reciprocal_tail_sum_le_log n) hT

end OnlineSteinerForest.UpperBound
