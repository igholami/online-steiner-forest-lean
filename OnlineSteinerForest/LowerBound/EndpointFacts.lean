import OnlineSteinerForest.LowerBound.OrderedMatching

/-! Matching ranks have distinct endpoints; an original vertex has at most one rank. -/
namespace OnlineSteinerForest.LowerBound

variable {m : ℕ} (σ : Equiv.Perm (Fin (2 * m)))

theorem leftEndpoint_injective : Function.Injective (leftEndpoint σ) := by
  intro i j he
  unfold leftEndpoint at he
  have hv := congrArg Fin.val (σ.injective he)
  change 2 * i.val = 2 * j.val at hv
  apply Fin.ext
  omega

theorem rightEndpoint_injective : Function.Injective (rightEndpoint σ) := by
  intro i j he
  unfold rightEndpoint at he
  have hv := congrArg Fin.val (σ.injective he)
  change 2 * i.val + 1 = 2 * j.val + 1 at hv
  apply Fin.ext
  omega

theorem leftEndpoint_ne_right (i j : Fin m) : leftEndpoint σ i ≠ rightEndpoint σ j := by
  intro he
  unfold leftEndpoint rightEndpoint at he
  have hv := congrArg Fin.val (σ.injective he)
  change 2 * i.val = 2 * j.val + 1 at hv
  omega

theorem endpoint_rank_unique (u : Fin (2 * m)) (i j : Fin m)
    (hi : u = leftEndpoint σ i ∨ u = rightEndpoint σ i)
    (hj : u = leftEndpoint σ j ∨ u = rightEndpoint σ j) : i = j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact leftEndpoint_injective σ (hi.symm.trans hj)
  · exact (leftEndpoint_ne_right σ i j (hi.symm.trans hj)).elim
  · exact (leftEndpoint_ne_right σ j i (hj.symm.trans hi)).elim
  · exact rightEndpoint_injective σ (hi.symm.trans hj)

end OnlineSteinerForest.LowerBound
