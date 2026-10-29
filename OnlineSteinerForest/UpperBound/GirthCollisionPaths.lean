import OnlineSteinerForest.UpperBound.GirthDartPaths
import OnlineSteinerForest.UpperBound.GirthWeightedCollision

/-! Two short nonbacktracking labelled walks with the same first dart and last vertex. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V] [Nonempty I]

theorem exists_short_collision (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (n : ℕ) (B : ℝ) (hB : 0 < B)
    (hmean : (n + 1 : ℕ) * (1 / (Fintype.card (Dart I) : ℝ)) * (2 * ∑ i, w i) ≤ B)
    (hsize : (Fintype.card (Dart I × V) : ℝ) *
      ((1 / (Fintype.card (Dart I) : ℝ)) * (1 / 2 : ℝ) ^ n) < 1 / 2) :
    ∃ p q : Paths (Dart I) n,
      p ≠ q ∧ Nonbacktracking left right n p ∧ Nonbacktracking left right n q ∧
      first n p = first n q ∧ head left right (last n p) = head left right (last n q) ∧
      walkCost w n p ≤ 2 * B ∧ walkCost w n q ≤ 2 * B := by
  classical
  let μ := walkProbability left right n
  let S := Finset.univ.filter (fun p => walkCost w n p ≤ 2 * B ∧ 0 < μ p)
  have hmass : 1 / 2 ≤ ∑ p ∈ S, μ p := by
    have hh := half_mass_below_double μ (walkCost w n)
      (walkProbability_nonneg left right n) (walkCost_nonneg w hw n)
      (sum_walkProbability left right hdegree n) B hB (by rw [expected_walkCost left right hdegree]; exact hmean)
    have heq : (∑ p ∈ S, μ p) =
        ∑ p ∈ Finset.univ.filter (fun p => walkCost w n p ≤ 2 * B), μ p := by
      simp only [S, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hc : walkCost w n p ≤ 2 * B
      · by_cases hp : 0 < μ p
        · simp [hc, hp]
        · have hz : μ p = 0 := le_antisymm (le_of_not_gt hp) (walkProbability_nonneg _ _ _ _)
          simp [hc, hp, hz]
      · simp [hc]
    rw [heq]
    exact hh
  obtain ⟨p, hp, q, hq, hpq, hkey⟩ := weighted_key_collision μ S
    (fun p => (first n p, head left right (last n p)))
    ((1 / (Fintype.card (Dart I) : ℝ)) * (1 / 2 : ℝ) ^ n)
    (by positivity) (by intro p _; exact walkProbability_le left right hdegree n p)
    (lt_of_lt_of_le hsize hmass)
  have hp' := (Finset.mem_filter.mp hp).2
  have hq' := (Finset.mem_filter.mp hq).2
  exact ⟨p, q, hpq, positive_walkProbability_nonbacktracking _ _ _ _ hp'.2,
    positive_walkProbability_nonbacktracking _ _ _ _ hq'.2,
    (Prod.mk.inj hkey).1, (Prod.mk.inj hkey).2, hp'.1, hq'.1⟩

end OnlineSteinerForest.UpperBound.Girth
