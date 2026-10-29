import OnlineSteinerForest.UpperBound.ZonesHubGraph
import OnlineSteinerForest.UpperBound.ZonesAttachments

/-! A boundary-hub edge obtains an actual original-graph attachment path. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V I C : Type*} [DecidableEq V]

/-- Route one selected hub spoke inside its concrete zone to the skeleton. -/
theorem exists_spoke_attachment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (outside : Set (Sym2 V))
    (zones : I → Finset (Sym2 V)) (zoneVertices : I → Set V) (component : I → C)
    (anchor : I → V) (root : C → V) (skeleton : Finset (Sym2 V)) (budget : ℝ)
    (hinput : ∀ i, ∀ e ∈ zones i, e ∈ G.edgeSet)
    (hzone : ∀ i v, v ∈ zoneVertices i →
      (SimpleGraph.fromEdgeSet (zones i : Set (Sym2 V))).Reachable v (anchor i))
    (hcost : ∀ i, edgeCost c (zones i) ≤ budget)
    (hskel : ∀ i, (SimpleGraph.fromEdgeSet (skeleton : Set (Sym2 V))).Reachable
      (anchor i) (root (component i)))
    {v : V} {q : C}
    (hspoke : (boundaryHubGraph outside zoneVertices component).Adj (.inl v) (.inr q)) :
    ∃ P : Finset (Sym2 V), (∀ e ∈ P, e ∈ G.edgeSet) ∧ edgeCost c P ≤ budget ∧
      (SimpleGraph.fromEdgeSet ((skeleton ∪ P : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
        v (root q) := by
  obtain ⟨i, hv, hi⟩ := (hub_spoke_iff outside zoneVertices component v q).mp hspoke
  obtain ⟨P, hp, _, hP⟩ := exists_zone_attachment c (zones i) (hinput i)
    (fun e he => hc e (hinput i e he)) (hzone i v hv)
  refine ⟨P, hp.subset_edgeSet, hP.trans (hcost i), ?_⟩
  have hpath := hp.reachable.mono (show
      SimpleGraph.fromEdgeSet (P : Set (Sym2 V)) ≤
      SimpleGraph.fromEdgeSet ((skeleton ∪ P : Finset (Sym2 V)) : Set (Sym2 V)) from
    fun _ _ h => ⟨Finset.mem_union_right _ h.1, h.2⟩)
  have hroot := (hskel i).mono (show
      SimpleGraph.fromEdgeSet (skeleton : Set (Sym2 V)) ≤
      SimpleGraph.fromEdgeSet ((skeleton ∪ P : Finset (Sym2 V)) : Set (Sym2 V)) from
    fun _ _ h => ⟨Finset.mem_union_left _ h.1, h.2⟩)
  rw [hi] at hroot
  exact hpath.trans hroot

end OnlineSteinerForest.UpperBound
