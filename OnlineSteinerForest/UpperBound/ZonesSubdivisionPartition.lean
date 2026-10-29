import OnlineSteinerForest.UpperBound.ZonesSubdivisionIterate
import OnlineSteinerForest.UpperBound.ZonesSubdivisionWeights
import OnlineSteinerForest.UpperBound.ZonesPartitionBuild
import OnlineSteinerForest.UpperBound.ZonesPartitionFinish

/-! Heavy edges can be subdivided before the complete connected-zone construction. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
universe u

/-- Every finite nonnegative-cost tree of cost at least `M` has a cost-preserving
subdivision partitioned into connected edge-disjoint zones costing `[M,3M]`.
The certificate records original marked vertices and recovery to whole original edges. -/
theorem exists_subdivided_tree_zonePartition {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M)
    (hlarge : M ≤ edgeCost c G.edgeFinset) :
    ∃ (W : Type u) (_ : Fintype W) (_ : DecidableEq W)
      (E : Finset (Sym2 W)) (d : Sym2 W → ℝ),
      (∀ e ∈ E, 0 ≤ d e) ∧ (∀ e ∈ E, ¬e.IsDiag) ∧
      Nonempty (ZoneSubdivisionCertificate G.edgeFinset c E d) ∧ Nonempty (ZonePartition E d M) := by
  let r := Classical.choice hG.nonempty
  obtain ⟨t, ht, he, _⟩ := exists_zoneTree G hG r
  have hmem : ∀ e ∈ t.edges, e ∈ G.edgeSet := by
    intro e h
    exact G.mem_edgeFinset.mp (he ▸ h)
  have hnd : ∀ e ∈ t.edges, ¬e.IsDiag := fun e he => G.not_isDiag_of_mem_edgeSet (hmem e he)
  have hct : ∀ e ∈ t.edges, 0 ≤ c e := fun e he => hc e (hmem e he)
  let C := edgeCost c t.edges
  have hC : ∀ e ∈ t.edges, c e ≤ C := by
    intro e he
    exact Finset.single_le_sum hct he
  obtain ⟨n, hn⟩ := exists_binary_subdivision_depth C M hM
  obtain ⟨W, hW, dW, s, T, d, hT, hndT, hcT, hCT, hcost, hcert⟩ :=
    exists_iterated_zoneSubdivision t ht hnd c hct C hC n
  letI := hW
  letI := dW
  have hbound : ∀ e ∈ T.edges, d e ≤ M := fun e he => (hCT e he).trans hn
  have hlargeT : M ≤ edgeCost d T.edges := by rw [hcost, he]; exact hlarge
  let H := SimpleGraph.fromEdgeSet (T.edges : Set (Sym2 W))
  have hH : ∀ e ∈ T.edges, e ∈ H.edgeSet := by
    intro e he
    simpa only [H, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff, Sym2.mem_diagSet, Finset.mem_coe] using
      And.intro he (hndT e he)
  let p := T.partition hT H hH d M hM hbound
  refine ⟨W, hW, dW, T.edges, d, hcT, hndT, ?_, p.complete hM (T.rooted hndT) hcT hlargeT⟩
  simpa only [he] using hcert

end OnlineSteinerForest.UpperBound
