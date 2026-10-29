import OnlineSteinerForest.UpperBound.ZonesForestPartition
import OnlineSteinerForest.UpperBound.ZonesForestEndpointEdges

/-! The common forest-zone family covers every large original endpoint and obeys the global zone-count budget. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem forest_partition_zone_subset (F : SimpleGraph V) (c : Sym2 V → ℝ) (M : ℝ) (n : ℕ)
    (p : ZonePartition (subdivisionEdges (largeForestEdges F c M) n) (subdivisionCost c n) M)
    (Z : Finset (Sym2 (subdivisionVertices V n))) (hZ : Z ∈ p.zones) :
    Z ⊆ subdivisionEdges F.edgeFinset n :=
  (p.zone_subset Z hZ).trans (subdivisionEdges_mono (largeForestEdges_subset F c M) n)

theorem forest_partition_covers_large_vertex (F : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (p : ZonePartition (subdivisionEdges (largeForestEdges F c M) n) (subdivisionCost c n) M)
    (r : V) (hr : M ≤ edgeCost c (componentEdges F (F.connectedComponentMk r))) :
    ∃ Z ∈ p.zones, zoneSupport Z (subdivisionEmbedding V n r) := by
  obtain ⟨e, he, hre⟩ := expanded_component_covers_vertex F c hc r (hM.trans_le hr) n
  have hsub : componentEdges F (F.connectedComponentMk r) ⊆ largeForestEdges F c M := by
    intro f hf
    exact Finset.mem_biUnion.mpr ⟨F.connectedComponentMk r, largeForestComponent_mem F c M r hr, hf⟩
  have he' := subdivisionEdges_mono hsub n he
  rw [← p.covers] at he'
  obtain ⟨Z, hZ, heZ⟩ := Finset.mem_biUnion.mp he'
  exact ⟨Z, hZ, e, heZ, hre⟩

theorem forest_partition_count (F : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (p : ZonePartition (subdivisionEdges (largeForestEdges F c M) n) (subdivisionCost c n) M) :
    (p.zones.card : ℝ) ≤ edgeCost c F.edgeFinset / M := by
  have hdis : (p.zones : Set (Finset (Sym2 (subdivisionVertices V n)))).PairwiseDisjoint id :=
    fun A hA B hB hAB => p.disjoint A hA B hB hAB
  have hlow : M * (p.zones.card : ℝ) ≤ edgeCost (subdivisionCost c n) (subdivisionEdges (largeForestEdges F c M) n) := by
    calc
      _ = ∑ _Z ∈ p.zones, M := by simp [mul_comm]
      _ ≤ ∑ Z ∈ p.zones, edgeCost (subdivisionCost c n) Z :=
        Finset.sum_le_sum (fun Z hZ => (p.good Z hZ).2.1)
      _ = _ := (zone_cost_sum (subdivisionCost c n) p.zones id hdis).trans
        (congrArg (edgeCost (subdivisionCost c n)) p.covers)
  have hnd : ∀ e ∈ F.edgeFinset, ¬e.IsDiag := fun e he => F.not_isDiag_of_mem_edgeSet (F.mem_edgeFinset.mp he)
  have hall := subdivisionProperties F.edgeFinset c hnd (fun e he => hc e (F.mem_edgeFinset.mp he)) n
  have hcost : edgeCost (subdivisionCost c n) (subdivisionEdges (largeForestEdges F c M) n) ≤ edgeCost c F.edgeFinset := by
    rw [← subdivisionCost_total F.edgeFinset c hnd n]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (subdivisionEdges_mono (largeForestEdges_subset F c M) n) (fun e he _ => (hall e he).2)
  apply (le_div_iff₀ hM).mpr
  nlinarith

end OnlineSteinerForest.UpperBound
