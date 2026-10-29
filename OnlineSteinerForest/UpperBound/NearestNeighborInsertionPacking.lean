import OnlineSteinerForest.UpperBound.NearestNeighborInsertion

/-! Insertions above a threshold, together with the initial point, form a separated set. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}

theorem newIndex_injective : Function.Injective (@newIndex n) := by
  intro i j hij
  have hval := congrArg Fin.val hij
  apply Fin.ext
  change i.val + 1 = j.val + 1 at hval
  omega

theorem insertion_threshold_packing (G : SimpleGraph V) (hG : G.IsTree)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (x : Fin (n + 1) → V)
    (J : Finset (Fin n)) (hJ : J.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : ∀ i ∈ J, δ ≤ insertionDistance G c hG.connected.preconnected x i) :
    ((J.card : ℝ) + 1) * δ ≤ 2 * edgeCost c G.edgeFinset := by
  let I : Finset (Fin (n + 1)) := insert 0 (J.image newIndex)
  have hzero : (0 : Fin (n + 1)) ∉ J.image newIndex := by
    intro he
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp he
    have hv := congrArg Fin.val heq
    change i.val + 1 = 0 at hv
    omega
  have hIcard : I.card = J.card + 1 := by
    rw [Finset.card_insert_of_notMem hzero, Finset.card_image_of_injective J newIndex_injective]
  have hclose : ∀ i ∈ I, ∀ j ∈ I, i.val < j.val →
      δ ≤ residualDistance G c ∅ (x j) (x i) (hG.connected.preconnected _ _) := by
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hj with hj | hj
    · subst j
      simp at hij
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
      exact (hlarge k hk).trans (insertionDistance_le_earlier G c hG.connected.preconnected x k i (by
        change i.val < k.val + 1 at hij
        omega))
  have hinj : Set.InjOn x (I : Set (Fin (n + 1))) := by
    intro i hi j hj heq
    rcases lt_trichotomy i.val j.val with hij | hij | hji
    · have hdist := hclose i hi j hj hij
      rw [originalDistance_eq_zero_of_eq G c hc hG.connected.preconnected _ _ heq.symm] at hdist
      linarith
    · exact Fin.ext hij
    · have hdist := hclose j hj i hi hji
      rw [originalDistance_eq_zero_of_eq G c hc hG.connected.preconnected _ _ heq] at hdist
      linarith
  let K := I.image x
  have hKcard : K.card = J.card + 1 := (Finset.card_image_of_injOn hinj).trans hIcard
  have hKtwo : 2 ≤ K.card := by rw [hKcard]; have := hJ.card_pos; omega
  have hsep : ∀ u ∈ K, ∀ v ∈ K, u ≠ v →
      δ ≤ residualDistance G c ∅ u v (hG.connected.preconnected u v) := by
    intro u hu v hv hne
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    rcases lt_trichotomy i.val j.val with hij | hij | hji
    · have hh := hclose i hi j hj hij
      rw [residualDistance_symm] at hh
      exact hh
    · exact (hne (congrArg x (Fin.ext hij))).elim
    · exact hclose j hj i hi hji
  have hp := tree_packing G hG c hc K hKtwo δ hsep
  simpa only [hKcard, Nat.cast_add, Nat.cast_one] using hp

end OnlineSteinerForest.UpperBound
