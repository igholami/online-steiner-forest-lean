import OnlineSteinerForest.UpperBound.ZonesForestMain

/-! Assemble the common expanded zone family directly from an actual original-edge reference forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_reference_forest_zones (G : SimpleGraph V) (old : Finset (Sym2 V))
    (hinput : ∀ e ∈ old, e ∈ G.edgeSet)
    (hforest : (SimpleGraph.fromEdgeSet (old : Set (Sym2 V))).IsAcyclic)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) :
    let F := SimpleGraph.fromEdgeSet (old : Set (Sym2 V))
    ∃ n : ℕ,
      ∃ cert : ZoneSubdivisionCertificate old c (subdivisionEdges old (n + 1)) (subdivisionCost c (n + 1)),
      ∃ p : ZonePartition (subdivisionEdges (largeForestEdges F c M) (n + 1)) (subdivisionCost c (n + 1)) M,
      cert.vertices = subdivisionEmbedding V (n + 1) ∧
      (∀ e ∈ subdivisionEdges old (n + 1), ¬e.IsDiag ∧ 0 ≤ subdivisionCost c (n + 1) e) ∧
      (∀ e : Sym2 V, Sym2.map cert.vertices e ∉ subdivisionEdges old (n + 1)) ∧
      (p.zones.card : ℝ) ≤ edgeCost c old / M ∧
      ∀ r : V, M ≤ referenceTreeCost old c r → ∃ Z ∈ p.zones, zoneSupport Z (cert.vertices r) := by
  let F := SimpleGraph.fromEdgeSet (old : Set (Sym2 V))
  have hFedge (inst : Fintype F.edgeSet) : @SimpleGraph.edgeFinset V F inst = old := by
    apply Finset.coe_injective
    rw [@SimpleGraph.coe_edgeFinset V F inst]
    ext e
    induction e using Sym2.ind with
    | _ u v =>
      change (s(u, v) ∈ old ∧ u ≠ v) ↔ s(u, v) ∈ old
      exact ⟨And.left, fun he => ⟨he, (hinput _ he).ne⟩⟩
  have hFc : ∀ e ∈ F.edgeSet, 0 ≤ c e := by
    intro e he
    have he' : e ∈ (old : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa only [F, SimpleGraph.edgeSet_fromEdgeSet] using he
    exact hc e (hinput e he'.1)
  obtain ⟨n, cert, p, hv, hprop, hsep, hcount, hcover⟩ := exists_uniform_forest_zones F hforest c hFc M hM
  let cert' := cert.congr (hFedge _) (congrArg (fun E => subdivisionEdges E (n + 1)) (hFedge _))
  refine ⟨n, cert', p, hv, ?_, ?_, ?_, ?_⟩
  · simpa only [hFedge] using hprop
  · simpa only [cert', ZoneSubdivisionCertificate.congr, hFedge] using hsep
  · simpa only [hFedge] using hcount
  · intro r hr
    apply hcover r
    simpa only [referenceTreeCost_eq_component_cost] using hr

end OnlineSteinerForest.UpperBound
