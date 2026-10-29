import OnlineSteinerForest.UpperBound.ZonesPartitionState

/-! Attach a bounded-weight parent edge to a child's small leftover. -/
namespace OnlineSteinerForest.UpperBound.ZonePartial

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V] {r s : V} {E : Finset (Sym2 V)}
  {c : Sym2 V → ℝ} {M : ℝ}

noncomputable def extend (p : ZonePartial s E c M) (hM : 0 < M) (hrs : r ≠ s)
    (hnew : s(r, s) ∉ E) (hsmall : c s(r, s) ≤ M) :
    ZonePartial r (insert s(r, s) E) c M := by
  let L := insert s(r, s) p.leftover
  have hne : s(r, s) ∉ p.leftover := fun he => hnew (p.leftover_subset he)
  have hcover : zoneUnion p.zones ∪ L = insert s(r, s) E := by
    dsimp [L]
    rw [Finset.union_insert, p.covers]
  have hdisj : (L :: p.zones).Pairwise Disjoint := by
    rw [List.pairwise_cons]
    refine ⟨?_, (List.pairwise_cons.mp p.disjoint).2⟩
    intro A hA
    exact Finset.disjoint_insert_left.mpr
      ⟨fun he => hnew (p.zone_subset hA he), p.left_disjoint hA⟩
  have hcost : edgeCost c L < 2 * M := by
    dsimp [L]
    rw [edgeCost, Finset.sum_insert hne]
    change c s(r, s) + edgeCost c p.leftover < _
    linarith [p.small]
  exact close r _ c M hM p.zones L hcover hdisj (p.rooted.extend hrs) hcost p.good

end OnlineSteinerForest.UpperBound.ZonePartial
