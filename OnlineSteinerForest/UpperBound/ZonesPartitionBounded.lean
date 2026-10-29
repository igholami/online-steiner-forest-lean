import OnlineSteinerForest.UpperBound.ZonesPartitionBuild
import OnlineSteinerForest.UpperBound.ZonesPartitionFamily

/-! Connected edge-disjoint zones of cost between `M` and `3M` for bounded-edge trees. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bottom-up construction followed by merging the root leftover. -/
theorem exists_tree_zonePartition (G : SimpleGraph V) (hG : G.IsTree)
    (c : Sym2 V → ℝ) (M : ℝ) (hM : 0 < M)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (hsmall : ∀ e ∈ G.edgeSet, c e ≤ M)
    (hlarge : M ≤ edgeCost c G.edgeFinset) : Nonempty (ZonePartition G.edgeFinset c M) := by
  let r := Classical.choice hG.nonempty
  obtain ⟨p⟩ := exists_zonePartial G hG r c M hM hsmall
  have hzones : p.zones ≠ [] := by
    intro hz
    have hcov := p.covers
    simp only [hz, zoneUnion_nil, Finset.empty_union] at hcov
    have hcost := congrArg (edgeCost c) hcov
    linarith [p.small]
  have hnonempty (F : Finset (Sym2 V)) (hF : F ∈ p.zones) : F.Nonempty := by
    by_contra hn
    have hzero : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hlo := (p.good F hF).2.1
    simp only [hzero, edgeCost, Finset.sum_empty] at hlo
    linarith
  have hex : ∃ F ∈ p.zones, F.Nonempty := by
    cases hz : p.zones with
    | nil => exact False.elim (hzones hz)
    | cons F Z =>
      refine ⟨F, by simp, ?_⟩
      exact hnonempty F (by simp [hz])
  have hcomplete : ∃ F ∈ p.zones, ZoneConnected (F ∪ p.leftover) := by
    by_cases hL : p.leftover.Nonempty
    · obtain ⟨F, hF, v, hvL, hvF⟩ :=
        exists_zone_shared_vertex G hG.connected p.leftover p.zones p.covers hL hex
      exact ⟨F, hF, (p.good F hF).1.union_shared p.rooted.connected hvF hvL⟩
    · obtain ⟨F, hF, _⟩ := hex
      refine ⟨F, hF, ?_⟩
      simpa only [Finset.not_nonempty_iff_eq_empty.mp hL, Finset.union_empty] using (p.good F hF).1
  obtain ⟨F, hF, hconn⟩ := hcomplete
  exact ⟨p.finish hM (fun e he => hc e (G.mem_edgeFinset.mp he)) F hF hconn⟩

end OnlineSteinerForest.UpperBound
