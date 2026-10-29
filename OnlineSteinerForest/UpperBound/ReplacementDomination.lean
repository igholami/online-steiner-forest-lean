import OnlineSteinerForest.UpperBound.ReplacementCenters
import OnlineSteinerForest.UpperBound.ReplacementAveraging
import Mathlib.Tactic.Ring
import OnlineSteinerForest.UpperBound.ReplacementProbabilityBound

/-! The small dominating center set used by the dense-zone replacement skeleton. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_small_neighborhood_hitting_set (N : V → Finset V)
    (hself : ∀ v, v ∈ N v) (hcard : ∀ v, 8192 ≤ (N v).card) :
    ∃ C : Finset V, (∀ v, ∃ u ∈ C, u ∈ N v) ∧ (C.card : ℝ) ≤ Fintype.card V / 512 := by
  have hmean : (∑ x : V → Bool, bernoulliWeight (1 / 1024) x *
      (augmentedCenters N x).card) ≤ Fintype.card V / 512 := by
    calc
      _ ≤ Fintype.card V * (1 / 1024 : ℝ) + ∑ v, (1 - (1 / 1024 : ℝ)) ^ (N v).card :=
        mean_augmented_card_le _ (by norm_num) (by norm_num) N
      _ ≤ Fintype.card V * (1 / 1024 : ℝ) + ∑ _v : V, (1 / 1024 : ℝ) :=
        add_le_add le_rfl (Finset.sum_le_sum (fun v _ => replacement_miss_probability_le _ (hcard v)))
      _ = _ := by simp [nsmul_eq_mul]; ring
  obtain ⟨x, hx⟩ := exists_le_weighted_bound (bernoulliWeight (1 / 1024))
    (fun x : V → Bool => ((augmentedCenters N x).card : ℝ))
    (bernoulliWeight_nonneg _ (by norm_num) (by norm_num)) (sum_bernoulliWeight _)
    (Fintype.card V / 512) hmean
  exact ⟨augmentedCenters N x, augmentedCenters_hit N hself x, hx⟩

/-- A graph of minimum degree at least `8191` admits the manuscript's center bound.
The proof also covers the empty graph without a separate nonempty hypothesis. -/
theorem exists_small_dominating_set (G : SimpleGraph V) (hdeg : ∀ v, 8191 ≤ G.degree v) :
    ∃ C : Finset V, (∀ v, v ∈ C ∨ ∃ u ∈ C, G.Adj v u) ∧
      (C.card : ℝ) ≤ Fintype.card V / 512 := by
  let N := fun v => insert v (G.neighborFinset v)
  have hself : ∀ v, v ∈ N v := by intro v; exact Finset.mem_insert_self _ _
  have hcard : ∀ v, 8192 ≤ (N v).card := by
    intro v
    dsimp only [N]
    rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self v),
      G.card_neighborFinset_eq_degree]
    exact Nat.succ_le_succ (hdeg v)
  obtain ⟨C, hC, hc⟩ := exists_small_neighborhood_hitting_set N hself hcard
  refine ⟨C, ?_, hc⟩
  intro v
  obtain ⟨u, hu, hNu⟩ := hC v
  rcases Finset.mem_insert.mp hNu with rfl | hNu
  · exact Or.inl hu
  · exact Or.inr ⟨u, hu, (G.mem_neighborFinset v u).mp hNu⟩

end OnlineSteinerForest.UpperBound
