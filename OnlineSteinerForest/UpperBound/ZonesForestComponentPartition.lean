import OnlineSteinerForest.UpperBound.ZonesForestComponentShape
import OnlineSteinerForest.UpperBound.ZonesForestSubdivisionSets
import OnlineSteinerForest.UpperBound.ZonesSubdivisionUniformCertificate
import OnlineSteinerForest.UpperBound.ZonesPartitionBuild
import OnlineSteinerForest.UpperBound.ZonesPartitionFinish

/-! Every large reference component is partitioned using one common subdivision type, depth, and cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem uniform_component_partition (F : SimpleGraph V) (hF : F.IsAcyclic) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) (n : ℕ)
    (hbound : ∀ e ∈ subdivisionEdges F.edgeFinset n, subdivisionCost c n e ≤ M)
    (C : F.ConnectedComponent) (hlarge : M ≤ edgeCost c (componentEdges F C)) :
    Nonempty (ZonePartition (subdivisionEdges (componentEdges F C) n) (subdivisionCost c n) M) := by
  obtain ⟨r, t, ht, he⟩ := exists_component_zoneTree F hF C
  let T := subdivisionShape t n
  have hnd : ∀ e ∈ t.edges, ¬e.IsDiag := by
    intro e he'
    exact F.not_isDiag_of_mem_edgeSet (F.mem_edgeFinset.mp (componentEdges_subset F C (he ▸ he')))
  have hvalid : T.Valid := subdivisionShape_valid t ht hnd n
  have hTE : T.edges = subdivisionEdges (componentEdges F C) n := by rw [subdivisionShape_edges, he]
  have hsub : T.edges ⊆ subdivisionEdges F.edgeFinset n := by
    rw [hTE]
    exact subdivisionEdges_mono (componentEdges_subset F C) n
  have hall := subdivisionProperties F.edgeFinset c
    (fun e he => F.not_isDiag_of_mem_edgeSet (F.mem_edgeFinset.mp he))
    (fun e he => hc e (F.mem_edgeFinset.mp he)) n
  have hnonloop : ∀ e ∈ T.edges, ¬e.IsDiag := fun e he => (hall e (hsub he)).1
  have hnonneg : ∀ e ∈ T.edges, 0 ≤ subdivisionCost c n e := fun e he => (hall e (hsub he)).2
  have hlargeT : M ≤ edgeCost (subdivisionCost c n) T.edges := by
    rw [hTE, subdivisionCost_total (componentEdges F C) c
      (fun e he => F.not_isDiag_of_mem_edgeSet (F.mem_edgeFinset.mp (componentEdges_subset F C he))) n]
    exact hlarge
  let H := SimpleGraph.fromEdgeSet (T.edges : Set (Sym2 (subdivisionVertices V n)))
  have hinput : ∀ e ∈ T.edges, e ∈ H.edgeSet := by
    intro e he'
    simpa only [H, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_diff, Finset.mem_coe, Sym2.mem_diagSet] using
      And.intro he' (hnonloop e he')
  let p := T.partition hvalid H hinput (subdivisionCost c n) M hM (fun e he => hbound e (hsub he))
  have hp := p.complete hM (T.rooted hnonloop) hnonneg hlargeT
  simpa only [hTE] using hp

end OnlineSteinerForest.UpperBound
