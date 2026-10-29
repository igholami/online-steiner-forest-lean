import OnlineSteinerForest.UpperBound.HistoryInvariant
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Sum actual retired and active cluster weights using the proved depth invariant. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*} [DecidableEq ι]

noncomputable def clusterWeight (w : ι → ℝ) (C : LabeledCluster ι) : ℝ := ∑ a ∈ C.members, w a

noncomputable def lifetimeMass (state : MergeHistory ι) (w : ι → ℝ) : ℝ :=
  (state.retired.map (clusterWeight w)).sum + ∑ C ∈ state.active, clusterWeight w C

theorem archived_mass_eq (retired : List (LabeledCluster ι)) (U : Finset ι) (w : ι → ℝ)
    (harchive : ∀ C ∈ retired, C.members ⊆ U) :
    (retired.map (clusterWeight w)).sum =
      ∑ a ∈ U, (((retired.filter (fun C => decide (a ∈ C.members))).length : ℕ) : ℝ) * w a := by
  classical
  induction retired with
  | nil => simp
  | cons C retired ih =>
    have hC : C.members ⊆ U := harchive C (by simp)
    have htail : ∀ D ∈ retired, D.members ⊆ U := fun D hD => harchive D (by simp [hD])
    have hfilter : U.filter (fun a => a ∈ C.members) = C.members := by
      ext a
      simp only [Finset.mem_filter]
      exact ⟨fun ha => ha.2, fun ha => ⟨hC ha, ha⟩⟩
    have hweight : clusterWeight w C = ∑ a ∈ U, if a ∈ C.members then w a else 0 := by
      rw [← Finset.sum_filter, hfilter]
      rfl
    simp only [List.map_cons, List.sum_cons]
    rw [ih htail, hweight, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    by_cases hmem : a ∈ C.members <;> simp [List.filter_cons, hmem, add_mul, add_comm]

theorem lifetimeMass_eq (state : MergeHistory ι) (U : Finset ι) (w : ι → ℝ)
    (h : HistoryInvariant state U) :
    lifetimeMass state w = ∑ a ∈ U, ((MergeHistory.retirementCount state a : ℝ) + 1) * w a := by
  have hactive : (∑ C ∈ state.active, clusterWeight w C) = ∑ a ∈ U, w a := by
    rw [← h.partition.cover, Finset.sum_biUnion (fun C hC D hD hCD => h.partition.disjoint C hC D hD hCD)]
    rfl
  rw [lifetimeMass, archived_mass_eq state.retired U w h.archive, hactive, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change _ * w a + w a = ((MergeHistory.retirementCount state a : ℝ) + 1) * w a
  simp only [MergeHistory.retirementCount]
  ring

/-- The full union-by-size lifetime mass estimate, derived from the implemented
merge operation and its depth invariant, with no mass-budget hypothesis. -/
theorem lifetimeMass_le_log2 (state : MergeHistory ι) (U : Finset ι) (w : ι → ℝ)
    (h : HistoryInvariant state U) (hw : ∀ a ∈ U, 0 ≤ w a) :
    lifetimeMass state w ≤ ((U.card.log2 : ℝ) + 1) * ∑ a ∈ U, w a := by
  rw [lifetimeMass_eq state U w h, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_right _ (hw a ha)
  exact add_le_add (Nat.cast_le.mpr (h.retirementCount_le_log2 a ha)) le_rfl

end OnlineSteinerForest.UpperBound
