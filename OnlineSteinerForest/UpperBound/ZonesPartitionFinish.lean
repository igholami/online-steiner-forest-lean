import OnlineSteinerForest.UpperBound.ZonesPartitionFamily
import OnlineSteinerForest.UpperBound.ZonesPartitionRootBoundary

/-! Final root processing for every edge-disjoint rooted branch expression. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V] [Fintype V]

theorem ZonePartial.complete {r : V} {E : Finset (Sym2 V)} {c : Sym2 V → ℝ} {M : ℝ}
    (p : ZonePartial r E c M) (hM : 0 < M) (hroot : ZoneRooted r E)
    (hc : ∀ e ∈ E, 0 ≤ c e) (hlarge : M ≤ edgeCost c E) :
    Nonempty (ZonePartition E c M) := by
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
        exists_zone_shared_vertex_rooted E r hroot p.leftover p.zones p.covers hL hex
      exact ⟨F, hF, (p.good F hF).1.union_shared p.rooted.connected hvF hvL⟩
    · obtain ⟨F, hF, _⟩ := hex
      refine ⟨F, hF, ?_⟩
      simpa only [Finset.not_nonempty_iff_eq_empty.mp hL, Finset.union_empty] using (p.good F hF).1
  obtain ⟨F, hF, hconn⟩ := hcomplete
  exact ⟨p.finish hM (fun e he => hc e he) F hF hconn⟩

end OnlineSteinerForest.UpperBound
