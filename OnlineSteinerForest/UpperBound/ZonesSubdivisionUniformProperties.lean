import OnlineSteinerForest.UpperBound.ZonesSubdivisionUniform

/-! Uniform global subdivision preserves valid trees, total costs and segment budgets. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false

open scoped Classical
universe u
variable {V : Type u} [DecidableEq V]

theorem subdivisionProperties (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hnd : ∀ e ∈ E, ¬e.IsDiag) (hc : ∀ e ∈ E, 0 ≤ c e) (n : ℕ) :
    ∀ e ∈ subdivisionEdges E n, ¬e.IsDiag ∧ 0 ≤ subdivisionCost c n e := by
  induction n with
  | zero => exact fun e he => ⟨hnd e he, hc e he⟩
  | succ n ih =>
    intro e he
    obtain ⟨f, hf, hndf, hweight⟩ := zoneSplitUnion_edge he
    refine ⟨hndf, ?_⟩
    change 0 ≤ zoneHalfCost (subdivisionCost c n) e
    rw [hweight]
    exact div_nonneg (ih f hf).2 (by norm_num)

theorem subdivisionCost_bound (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (C : ℝ)
    (hC : ∀ e ∈ E, c e ≤ C) (n : ℕ) :
    ∀ e ∈ subdivisionEdges E n, subdivisionCost c n e ≤ C / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
    intro e he
    change c e ≤ C / 1
    simpa only [div_one] using hC e he
  | succ n ih =>
    intro e he
    obtain ⟨f, hf, _, hweight⟩ := zoneSplitUnion_edge he
    change zoneHalfCost (subdivisionCost c n) e ≤ _
    rw [hweight]
    calc
      _ ≤ (C / (2 : ℝ) ^ n) / 2 := div_le_div_of_nonneg_right (ih f hf) (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem subdivisionCost_total (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hnd : ∀ e ∈ E, ¬e.IsDiag) (n : ℕ) :
    edgeCost (subdivisionCost c n) (subdivisionEdges E n) = edgeCost c E := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn : ∀ e ∈ subdivisionEdges E n, ¬e.IsDiag :=
      fun e he => (subdivisionProperties E (fun _ => 0) hnd (by simp) n e he).1
    exact (zoneSplitUnion_cost (subdivisionEdges E n) (subdivisionCost c n) hn).trans ih

theorem subdivisionShape_valid {r : V} (t : ZoneTree V r) (ht : t.Valid)
    (hnd : ∀ e ∈ t.edges, ¬e.IsDiag) (n : ℕ) : (subdivisionShape t n).Valid := by
  induction n with
  | zero => exact ht
  | succ n ih =>
    apply ZoneTree.valid_subdivide _ ih
    intro e he
    rw [subdivisionShape_edges] at he
    exact (subdivisionProperties t.edges (fun _ => 0) hnd (by simp) n e he).1

end OnlineSteinerForest.UpperBound
