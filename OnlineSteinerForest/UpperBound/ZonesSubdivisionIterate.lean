import OnlineSteinerForest.UpperBound.ZonesSubdivisionProperties
import OnlineSteinerForest.UpperBound.ZonesSubdivisionCertificate

/-! Iterated private-midpoint subdivision preserves total cost and bounds every segment. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
universe u

theorem exists_iterated_zoneSubdivision {V : Type u} [Fintype V] [DecidableEq V]
    {r : V} (t : ZoneTree V r) (ht : t.Valid) (hnd : ∀ e ∈ t.edges, ¬e.IsDiag)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ t.edges, 0 ≤ c e) (C : ℝ)
    (hC : ∀ e ∈ t.edges, c e ≤ C) (n : ℕ) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W) (s : W)
      (T : ZoneTree W s) (d : Sym2 W → ℝ),
      T.Valid ∧ (∀ e ∈ T.edges, ¬e.IsDiag) ∧ (∀ e ∈ T.edges, 0 ≤ d e) ∧
      (∀ e ∈ T.edges, d e ≤ C / (2 : ℝ) ^ n) ∧ edgeCost d T.edges = edgeCost c t.edges ∧
      Nonempty (ZoneSubdivisionCertificate t.edges c T.edges d) := by
  induction n with
  | zero => exact ⟨V, inferInstance, inferInstance, r, t, c, ht, hnd, hc, by simpa using hC, rfl, ⟨ZoneSubdivisionCertificate.refl _ _⟩⟩
  | succ n ih =>
    obtain ⟨W, hW, dW, s, T, d, hT, hndT, hcT, hCT, hcostT, hcertT⟩ := ih
    letI := hW
    letI := dW
    refine ⟨ZoneSubdivisionVertex W, inferInstance, inferInstance, Sum.inl s,
      T.subdivide, zoneHalfCost d, T.valid_subdivide hT hndT, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      rw [ZoneTree.edges_subdivide] at he
      exact (zoneSplitUnion_edge he).choose_spec.2.1
    · intro e he
      rw [ZoneTree.edges_subdivide] at he
      obtain ⟨f, hf, _, hweight⟩ := zoneSplitUnion_edge he
      rw [hweight]
      exact div_nonneg (hcT f hf) (by norm_num)
    · intro e he
      rw [ZoneTree.edges_subdivide] at he
      obtain ⟨f, hf, _, hweight⟩ := zoneSplitUnion_edge he
      rw [hweight]
      calc
        _ ≤ (C / (2 : ℝ) ^ n) / 2 := div_le_div_of_nonneg_right (hCT f hf) (by norm_num)
        _ = _ := by rw [pow_succ]; ring
    · rw [ZoneTree.edges_subdivide, zoneSplitUnion_cost _ d hndT, hcostT]
    · have hcert := (Classical.choice hcertT).trans
        (ZoneSubdivisionCertificate.midpoint T.edges d hcT hndT)
      rw [← T.edges_subdivide] at hcert
      exact ⟨hcert⟩

end OnlineSteinerForest.UpperBound
