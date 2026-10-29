import OnlineSteinerForest.UpperBound.ZonesForestCoverageCount
import OnlineSteinerForest.UpperBound.ZonesSubdivisionWeights

/-! One globally expanded reference forest supplies all large-component zones and every original endpoint. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_uniform_forest_zones (F : SimpleGraph V) (hF : F.IsAcyclic)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ F.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) :
    ∃ n : ℕ,
      ∃ cert : ZoneSubdivisionCertificate F.edgeFinset c (subdivisionEdges F.edgeFinset (n + 1)) (subdivisionCost c (n + 1)),
      ∃ p : ZonePartition (subdivisionEdges (largeForestEdges F c M) (n + 1)) (subdivisionCost c (n + 1)) M,
      cert.vertices = subdivisionEmbedding V (n + 1) ∧
      (∀ e ∈ subdivisionEdges F.edgeFinset (n + 1), ¬e.IsDiag ∧ 0 ≤ subdivisionCost c (n + 1) e) ∧
      (∀ e : Sym2 V, Sym2.map cert.vertices e ∉ subdivisionEdges F.edgeFinset (n + 1)) ∧
      (p.zones.card : ℝ) ≤ edgeCost c F.edgeFinset / M ∧
      ∀ r : V, M ≤ edgeCost c (componentEdges F (F.connectedComponentMk r)) →
        ∃ Z ∈ p.zones, zoneSupport Z (cert.vertices r) := by
  let cap := edgeCost c F.edgeFinset
  have hnd : ∀ e ∈ F.edgeFinset, ¬e.IsDiag := fun e he => F.not_isDiag_of_mem_edgeSet (F.mem_edgeFinset.mp he)
  have hn : ∀ e ∈ F.edgeFinset, 0 ≤ c e := fun e he => hc e (F.mem_edgeFinset.mp he)
  have hcap : ∀ e ∈ F.edgeFinset, c e ≤ cap := fun e he => Finset.single_le_sum hn he
  obtain ⟨n, hdepth⟩ := exists_binary_subdivision_depth cap M hM
  have hextra : cap / (2 : ℝ) ^ (n + 1) ≤ M := by
    rw [show cap / (2 : ℝ) ^ (n + 1) = (cap / (2 : ℝ) ^ n) / 2 by rw [pow_succ]; ring]
    linarith
  have hbound : ∀ e ∈ subdivisionEdges F.edgeFinset (n + 1), subdivisionCost c (n + 1) e ≤ M :=
    fun e he => (subdivisionCost_bound F.edgeFinset c cap hcap (n + 1) e he).trans hextra
  let cert := uniformSubdivisionCertificate F.edgeFinset c hnd hn (n + 1)
  let p := Classical.choice (uniform_large_forest_partition F hF c hc M hM (n + 1) hbound)
  have hvertices : cert.vertices = subdivisionEmbedding V (n + 1) :=
    uniformSubdivisionCertificate_vertices F.edgeFinset c hnd hn (n + 1)
  refine ⟨n, cert, p, hvertices, subdivisionProperties F.edgeFinset c hnd hn (n + 1), ?_,
    forest_partition_count F c hc M hM (n + 1) p, ?_⟩
  · intro e
    rw [hvertices]
    exact subdivisionEmbedding_separated F.edgeFinset n e
  · intro r hr
    rw [hvertices]
    exact forest_partition_covers_large_vertex F c hc M hM (n + 1) p r hr

end OnlineSteinerForest.UpperBound
