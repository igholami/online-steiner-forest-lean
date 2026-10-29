import OnlineSteinerForest.UpperBound.GirthConnectedReduction
import OnlineSteinerForest.UpperBound.GirthComponentSums
import OnlineSteinerForest.UpperBound.GirthComponentAverage
import OnlineSteinerForest.UpperBound.GirthMapCollision

/-! The manuscript weighted cycle-rank lemma, including disconnected labelled multigraphs. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem weighted_collision_rank_bound (left right : I → V) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hr : 1 ≤ cycleRank left right) :
    ∃ p : Collision left right, p.cost w ≤
      4 * cycleFactor (cycleRank left right) * (∑ i, w i) / cycleRank left right := by
  classical
  let r := fun C : (endpointGraph left right).ConnectedComponent =>
    cycleRank (componentLeft left right C) (componentRight left right C)
  let c := fun C : (endpointGraph left right).ConnectedComponent => ∑ i : ComponentEdges left right C, w i.val
  have hc : ∀ C, 0 ≤ c C := by intro C; exact Finset.sum_nonneg (by intro i _; exact hw i.val)
  have hsumr : ∑ C, r C = cycleRank left right := sum_component_ranks left right
  have hsumc : ∑ C, c C = ∑ i, w i := sum_component_costs left right w
  obtain ⟨C, hpos, hcross⟩ := exists_positive_rank_ratio r c hc (by rw [hsumr]; omega)
  have hsumr' : (∑ C, (r C : ℝ)) = (cycleRank left right : ℝ) := by exact_mod_cast hsumr
  rw [hsumr', hsumc] at hcross
  have hR : r C ≤ cycleRank left right := by
    rw [← hsumr]
    exact Finset.single_le_sum (by intro D _; exact Nat.zero_le _) (Finset.mem_univ C)
  have hmono := cycleFactor_mono hpos hR
  have hpos' : (0 : ℝ) < r C := by exact_mod_cast hpos
  have hr' : (0 : ℝ) < cycleRank left right := by exact_mod_cast hr
  have hratio : c C / (r C : ℝ) ≤ (∑ i, w i) / cycleRank left right :=
    (div_le_div_iff₀ hpos' hr').mpr (by simpa [mul_comm] using hcross)
  obtain ⟨p, hp⟩ := connected_collision_bound (componentLeft left right C) (componentRight left right C)
    (fun i => w i.val) (by intro i; exact hw i.val) (component_endpoint_connected left right C) hpos
  let P := p.map left right Subtype.val Subtype.val Subtype.coe_injective (fun _ => rfl) (fun _ => rfl)
  refine ⟨P, ?_⟩
  calc
    P.cost w = p.cost (fun i => w i.val) := p.map_cost _ _ _ _ _ _ _ _
    _ ≤ 4 * cycleFactor (r C) * c C / (r C : ℝ) := hp
    _ = (4 * (cycleFactor (r C) : ℝ)) * (c C / (r C : ℝ)) := by ring
    _ ≤ (4 * (cycleFactor (cycleRank left right) : ℝ)) * ((∑ i, w i) / cycleRank left right) :=
      mul_le_mul (by exact_mod_cast Nat.mul_le_mul_left 4 hmono) hratio
        (div_nonneg (hc C) hpos'.le) (by positivity)
    _ = _ := by ring

/-- A finite weighted labelled multigraph of rank `r≥1` has a standard simple-graph cycle
in its canonical subdivision costing at most `4 H(r) C/r`. -/
theorem weighted_cycle_rank_bound (left right : I → V) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hr : 1 ≤ cycleRank left right) :
    ∃ z, ∃ p : (edgeSubdivision left right).Walk z z, p.IsCycle ∧
      (p.edges.map (subdivisionCost w)).sum ≤
        4 * cycleFactor (cycleRank left right) * (∑ i, w i) / cycleRank left right := by
  obtain ⟨p, hp⟩ := weighted_collision_rank_bound left right w hw hr
  obtain ⟨z, c, hc, hcost⟩ := p.exists_cycle w hw
  exact ⟨z, c, hc, hcost.trans hp⟩

end OnlineSteinerForest.UpperBound.Girth
