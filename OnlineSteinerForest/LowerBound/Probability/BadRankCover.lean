import OnlineSteinerForest.LowerBound.Probability.BadRank
import OnlineSteinerForest.LowerBound.Probability.VariableCover
import OnlineSteinerForest.LowerBound.Trace.BadPattern
import OnlineSteinerForest.LowerBound.PatternSize

/-! Every failed distance test is covered by a finite weighted endpoint pattern. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem badRankProbability_le_patterns (h : ℕ) (hh : 32 ≤ h)
    (i : Fin (matchingSize h)) (hi : firstRank h ≤ i.val + 1) :
    badRankProbability h i ≤
      ∑ p : Pattern h i, p.2.val.weight *
        (2 / (2 * (matchingSize h : ℝ)) ^ (2 * p.1.val + 2)) := by
  let : Nonempty (Fin (2 * matchingSize h)) := ⟨⟨0, by omega⟩⟩
  have hc := variable_cover_probability_le
    (fun σ => ¬ GoodRank h σ i)
    (fun p : Pattern h i => 2 * p.1.val + 2)
    (fun p => boundaryTuple i p.2.val.ranks p.2.val.flip)
    (fun p => p.2.val.imageTuple p.2.property)
    (fun p => p.2.val.weight) (fun p => p.2.val.weight_nonneg)
    (fun σ hbad => by
      obtain ⟨q, p, hp, himage, hw⟩ := Trace.exists_pattern_of_bad_rank h hh σ i hi hbad
      exact ⟨⟨q, ⟨p, hp⟩⟩, himage, hw⟩)
    (fun p => by
      simpa only [Fintype.card_fin, twice_matchingSize h] using
        pattern_constraint_sq_le h hh p.1.val (by omega))
  unfold badRankProbability
  convert hc using 1
  · simp only [sum_indicator_eq_card, ← Nat.card_eq_fintype_card]
  · simp only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]

end OnlineSteinerForest.LowerBound.Probability
