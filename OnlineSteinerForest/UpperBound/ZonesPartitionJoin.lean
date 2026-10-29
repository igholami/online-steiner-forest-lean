import OnlineSteinerForest.UpperBound.ZonesPartitionState

/-! Combine two edge-disjoint child collections at a shared root. -/
namespace OnlineSteinerForest.UpperBound.ZonePartial

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V] {r : V} {E F : Finset (Sym2 V)}
  {c : Sym2 V → ℝ} {M : ℝ}

noncomputable def join (p : ZonePartial r E c M) (q : ZonePartial r F c M)
    (hM : 0 < M) (hEF : Disjoint E F) : ZonePartial r (E ∪ F) c M := by
  let Z := p.zones ++ q.zones
  let L := p.leftover ∪ q.leftover
  have hleft : Disjoint p.leftover q.leftover := hEF.mono p.leftover_subset q.leftover_subset
  have hcover : zoneUnion Z ∪ L = E ∪ F := by
    dsimp [Z, L]
    rw [zoneUnion_append]
    calc
      _ = (zoneUnion p.zones ∪ p.leftover) ∪ (zoneUnion q.zones ∪ q.leftover) := by
        ext e
        simp only [Finset.mem_union]
        tauto
      _ = _ := congrArg₂ (fun A B : Finset (Sym2 V) => A ∪ B) p.covers q.covers
  have hdisj : (L :: Z).Pairwise Disjoint := by
    rw [List.pairwise_cons]
    constructor
    · intro A hA
      change A ∈ p.zones ++ q.zones at hA
      rcases List.mem_append.mp hA with hA | hA
      · exact Finset.disjoint_union_left.mpr ⟨p.left_disjoint hA,
          (hEF.mono (p.zone_subset hA) q.leftover_subset).symm⟩
      · exact Finset.disjoint_union_left.mpr
          ⟨hEF.mono p.leftover_subset (q.zone_subset hA), q.left_disjoint hA⟩
    · change (p.zones ++ q.zones).Pairwise Disjoint
      rw [List.pairwise_append]
      exact ⟨(List.pairwise_cons.mp p.disjoint).2, (List.pairwise_cons.mp q.disjoint).2,
        fun A hA B hB => hEF.mono (p.zone_subset hA) (q.zone_subset hB)⟩
  have hcost : edgeCost c L < 2 * M := by
    dsimp [L]
    rw [edgeCost, Finset.sum_union hleft]
    change edgeCost c p.leftover + edgeCost c q.leftover < _
    linarith [p.small, q.small]
  apply close r (E ∪ F) c M hM Z L hcover hdisj (p.rooted.union q.rooted) hcost
  intro A hA
  rcases List.mem_append.mp hA with hA | hA
  · exact p.good A hA
  · exact q.good A hA

end OnlineSteinerForest.UpperBound.ZonePartial
