import OnlineSteinerForest.UpperBound.ZonesForestMain
import OnlineSteinerForest.UpperBound.SmallReferenceCost

/-! Actual reference edge sets have one common subdivision covering all large endpoints. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

set_option backward.isDefEq.respectTransparency.types false
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem retained_forest_zones (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ G.edgeSet)
    (hforest : (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).IsAcyclic)
    (c : Sym2 V → ℝ) (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (M : ℝ) (hM : 0 < M) :
    ∃ n : ℕ,
      ∃ cert : ZoneSubdivisionCertificate E c (subdivisionEdges E (n+1)) (subdivisionCost c (n+1)),
      ∃ A : Finset (Sym2 (subdivisionVertices V (n+1))),
      ∃ p : ZonePartition A (subdivisionCost c (n+1)) M,
        (∀ Z ∈ p.zones, Z ⊆ subdivisionEdges E (n+1)) ∧
        (∀ e ∈ subdivisionEdges E (n+1), ¬e.IsDiag ∧ 0 ≤ subdivisionCost c (n+1) e) ∧
        (∀ e : Sym2 V, Sym2.map cert.vertices e ∉ subdivisionEdges E (n+1)) ∧
        (p.zones.card : ℝ) * M ≤ edgeCost c E ∧
        (∀ r : V, M ≤ referenceTreeCost E c r →
          ∃ Z ∈ p.zones, zoneSupport Z (cert.vertices r)) := by
  let H := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  have hedge (inst : Fintype H.edgeSet) : @SimpleGraph.edgeFinset V H inst = E := by
    ext e
    simp only [SimpleGraph.edgeFinset, Set.mem_toFinset]
    induction e using Sym2.ind with
    | _ u v => exact ⟨And.left, fun he => ⟨he, (hE _ he).ne⟩⟩
  have hnonneg : ∀ e ∈ H.edgeSet, 0 ≤ c e := by
    intro e he
    exact hc e (hE e (by
      have he' : e ∈ (E : Set (Sym2 V)) \ Sym2.diagSet := by simpa only [H, SimpleGraph.edgeSet_fromEdgeSet] using he
      exact he'.1))
  obtain ⟨n, cert, p, hv, hprop, hsep, hcount, hcover⟩ :=
    exists_uniform_forest_zones H hforest c hnonneg M hM
  have hsub := forest_partition_zone_subset H c M (n+1) p
  let cert' := cert.congr (hedge _) (congrArg (fun X => subdivisionEdges X (n+1)) (hedge _))
  have hprop' : ∀ e ∈ subdivisionEdges E (n+1), ¬ e.IsDiag ∧ 0 ≤ subdivisionCost c (n+1) e := by simpa only [hedge] using hprop
  have hsep' : ∀ e : Sym2 V, Sym2.map cert'.vertices e ∉ subdivisionEdges E (n+1) := by simpa only [cert', ZoneSubdivisionCertificate.congr, hedge] using hsep
  have hsub' : ∀ Z ∈ p.zones, Z ⊆ subdivisionEdges E (n+1) := by simpa only [hedge] using hsub
  have hcount' : (p.zones.card : ℝ) ≤ edgeCost c E / M := by simpa only [hedge] using hcount
  refine ⟨n, cert', _, p, hsub', hprop', hsep', ?_, ?_⟩
  · exact (le_div_iff₀ hM).mp hcount'
  · intro r hr
    apply hcover r
    exact (referenceTreeCost_eq_component_cost E c r) ▸ hr

end OnlineSteinerForest.UpperBound
