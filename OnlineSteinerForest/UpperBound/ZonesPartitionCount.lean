import OnlineSteinerForest.UpperBound.ZonesPartitionFamily
import OnlineSteinerForest.UpperBound.ZonesCost

/-! The manuscript's zone-count consequence for the constructed partition. -/
namespace OnlineSteinerForest.UpperBound.ZonePartition

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [DecidableEq V] {E : Finset (Sym2 V)}
  {c : Sym2 V → ℝ} {M : ℝ}

theorem cost_sum (p : ZonePartition E c M) :
    (∑ F ∈ p.zones, edgeCost c F) = edgeCost c E := by
  have hd : (p.zones : Set (Finset (Sym2 V))).PairwiseDisjoint id := by
    intro F hF H hH hne
    exact p.disjoint F hF H hH hne
  simpa only [p.covers, id_eq] using zone_cost_sum c p.zones id hd

theorem count_le_cost_div (p : ZonePartition E c M) (hM : 0 < M) :
    (p.zones.card : ℝ) ≤ edgeCost c E / M := by
  apply (le_div_iff₀ hM).mpr
  calc
    (p.zones.card : ℝ) * M = ∑ _F ∈ p.zones, M := by simp
    _ ≤ ∑ F ∈ p.zones, edgeCost c F := Finset.sum_le_sum (fun F hF => (p.good F hF).2.1)
    _ = edgeCost c E := p.cost_sum

theorem subset_edges (p : ZonePartition E c M) {F : Finset (Sym2 V)} (hF : F ∈ p.zones) :
    F ⊆ E := by
  intro e he
  rw [← p.covers]
  exact Finset.mem_biUnion.mpr ⟨F, hF, he⟩

end OnlineSteinerForest.UpperBound.ZonePartition
