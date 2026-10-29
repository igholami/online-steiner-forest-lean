import OnlineSteinerForest.UpperBound.NearestNeighborSpacing

/-! A finite cyclic packing estimate using actual increasing tour positions. -/
namespace OnlineSteinerForest.UpperBound

theorem finite_cyclic_packing (I : Finset ℕ) (F : ℕ → ℝ) (r T : ℝ) (hcard : 2 ≤ I.card)
    (hforward : ∀ i ∈ I, ∀ j ∈ I, i < j → r ≤ F j - F i)
    (hwrap : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → r ≤ T - F j + F i) :
    (I.card : ℝ) * r ≤ T := by
  have hsort := I.sortedLT_sort.pairwise
  have hmem : ∀ i ∈ I.sort (· ≤ ·), i ∈ I := fun i hi => (Finset.mem_sort _).mp hi
  have hpair : (I.sort (· ≤ ·)).Pairwise (fun i j => F i + r ≤ F j) := by
    apply List.Pairwise.imp_of_mem _ hsort
    intro i j hi hj hij
    linarith [hforward i (hmem i hi) j (hmem j hj) hij]
  have hlen : (I.sort (· ≤ ·)).length = I.card := by simp
  cases heq : I.sort (· ≤ ·) with
  | nil => simp only [heq, List.length_nil] at hlen; omega
  | cons a xs =>
    cases xs with
    | nil => simp only [heq, List.length_cons, List.length_nil] at hlen; omega
    | cons b xs =>
      rw [heq] at hsort hpair hmem hlen
      let last := (b :: xs).getLastD a
      have hlast : last ∈ b :: xs := lastD_mem_of_ne_nil a (b :: xs) (by simp)
      have halt : a < last := (List.pairwise_cons.mp hsort).1 last hlast
      have hspacing := pairwise_spacing_bound F r a (b :: xs) hpair
      have hclosing := hwrap a (hmem a (by simp)) last
        (hmem last (List.mem_cons_of_mem _ hlast)) (ne_of_lt halt)
      have hlength : (I.card : ℝ) = ((b :: xs).length : ℝ) + 1 := by
        have hnat : I.card = (b :: xs).length + 1 := by simpa only [List.length_cons] using hlen.symm
        exact_mod_cast hnat
      rw [hlength]
      change (((b :: xs).length : ℝ) + 1) * r ≤ T
      change ((b :: xs).length : ℝ) * r ≤ F last - F a at hspacing
      nlinarith

end OnlineSteinerForest.UpperBound
