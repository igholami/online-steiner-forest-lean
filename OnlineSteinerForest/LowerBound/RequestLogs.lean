import OnlineSteinerForest.LowerBound.RequestGrowth

/-! Bound request-count logarithms by the construction's natural size parameters. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

theorem instance_requests_le_vertexCount (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    (instanceRequests h σ).length ≤ vertexCount h := by
  have hc := (retainedRanks h σ).card_le_univ
  simp only [Fintype.card_fin] at hc
  have hm := twice_matchingSize h
  simpa only [instanceRequests, requestedPairs_length] using
    hc.trans (show matchingSize h ≤ vertexCount h by omega)

theorem instance_request_log_bounds (h : ℕ) (hh : 32 ≤ h)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (hσ : RetainsHalf h σ) :
    0 ≤ Real.log (instanceRequests h σ).length ∧
      Real.log (instanceRequests h σ).length ≤ (logSize h : ℝ) * Real.log 2 ∧
      Real.log (Real.log (instanceRequests h σ).length) ≤ (h : ℝ) * Real.log 2 := by
  have hg := instance_request_count_ge_level h hh σ hσ
  have hk32 : 32 ≤ (instanceRequests h σ).length := hh.trans hg
  have hkpos : (0 : ℝ) < (instanceRequests h σ).length := Nat.cast_pos.mpr (by omega)
  have hlogpos : 0 < Real.log (instanceRequests h σ).length := Real.log_pos
    (Nat.one_lt_cast.mpr (by omega))
  have hlog := Real.log_le_log hkpos (Nat.cast_le.mpr (instance_requests_le_vertexCount h σ))
  simp only [vertexCount, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hlog
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    norm_num at ht
    exact ht
  have hlogL : Real.log (instanceRequests h σ).length ≤ (logSize h : ℝ) := by
    calc
      _ ≤ (logSize h : ℝ) * Real.log 2 := hlog
      _ ≤ (logSize h : ℝ) * 1 := mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
      _ = _ := mul_one _
  have hloglog := Real.log_le_log hlogpos hlogL
  simp only [logSize, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow] at hloglog
  exact ⟨hlogpos.le, hlog, hloglog⟩

end OnlineSteinerForest.LowerBound
