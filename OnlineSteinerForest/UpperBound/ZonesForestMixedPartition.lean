import OnlineSteinerForest.UpperBound.ZonesForestJoin
import OnlineSteinerForest.UpperBound.ZonesSubdivisionMixedCost

/-! The same reference-zone data keeps its exact budgets in the expanded mixed ambient cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

noncomputable def ZonePartition.changeCost {E : Finset (Sym2 W)} {c : Sym2 W → ℝ} {M : ℝ}
    (p : ZonePartition E c M) (d : Sym2 W → ℝ) (hd : ∀ e ∈ E, d e = c e) : ZonePartition E d M where
  zones := p.zones
  covers := p.covers
  disjoint := p.disjoint
  good Z hZ := by
    have heq : edgeCost d Z = edgeCost c Z :=
      Finset.sum_congr rfl (fun e he => hd e (p.zone_subset Z hZ he))
    obtain ⟨hconn, hlo, hhi⟩ := p.good Z hZ
    refine ⟨hconn, ?_, ?_⟩
    · rw [heq]; exact hlo
    · rw [heq]; exact hhi

noncomputable def ZonePartition.mixedCost {E F : Finset (Sym2 W)} {d : Sym2 W → ℝ}
    {M : ℝ} (p : ZonePartition E d M) (f : V ↪ W) (c : Sym2 V → ℝ) (hEF : E ⊆ F) :
    ZonePartition E (mixedSubdivisionCost f F d c) M :=
  p.changeCost _ (fun e he => mixedSubdivisionCost_reference f F d c (hEF he))

end OnlineSteinerForest.UpperBound
