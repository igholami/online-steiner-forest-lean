import OnlineSteinerForest.UpperBound.ZonesHubRequired
import OnlineSteinerForest.UpperBound.ZonesHubAttachments
import OnlineSteinerForest.UpperBound.ZonesHubRouting

/-! Boundary-hub trees yield bounded-cost attachments preserving all marked connections. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V I C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

theorem exists_marked_attachments (G F : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (kept skeleton : Finset (Sym2 V))
    (zones : I → Finset (Sym2 V)) (zoneVertices : I → Set V) (component : I → C)
    (anchor : I → V) (root : C → V) (marks : Finset V)
    (budget : ℝ) (hbudget : 0 ≤ budget)
    (hinput : ∀ i, ∀ e ∈ zones i, e ∈ G.edgeSet)
    (hzone : ∀ i v, v ∈ zoneVertices i →
      (SimpleGraph.fromEdgeSet (zones i : Set (Sym2 V))).Reachable v (anchor i))
    (hcost : ∀ i, edgeCost c (zones i) ≤ budget)
    (hskel : ∀ i, (SimpleGraph.fromEdgeSet (skeleton : Set (Sym2 V))).Reachable
      (anchor i) (root (component i)))
    (hcover : ∀ u v, F.Adj u v → s(u, v) ∈ kept ∨
      ∃ i, u ∈ zoneVertices i ∧ v ∈ zoneVertices i) :
    ∃ A : Finset (Sym2 V), (∀ e ∈ A, e ∈ G.edgeSet) ∧
      edgeCost c A ≤ 2 * ((Fintype.card C : ℝ) + marks.card) * budget ∧
      ∀ u ∈ marks, ∀ v ∈ marks, F.Reachable u v →
        (SimpleGraph.fromEdgeSet ((kept ∪ skeleton ∪ A : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
          u v := by
  let B := boundaryHubGraph (kept : Set (Sym2 V)) zoneVertices component
  obtain ⟨H, hHB, hconnect, hdegree⟩ := exists_marked_hub_subgraph B marks
  obtain ⟨A, hA, hcostA, hspokes⟩ := exists_hub_attachments G c hc
    (kept : Set (Sym2 V)) zones zoneVertices component anchor root skeleton budget
    hbudget hinput hzone hcost hskel H hHB
  refine ⟨A, hA, hcostA.trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hbudget
    exact_mod_cast hdegree
  · intro u hu v hv huv
    let R := SimpleGraph.fromEdgeSet
      ((kept ∪ skeleton ∪ A : Finset (Sym2 V)) : Set (Sym2 V))
    have hselected : H.Reachable (.inl u) (.inl v) :=
      hconnect u hu v hv (boundaryHub_preserves_reachable F
        (kept : Set (Sym2 V)) zoneVertices component hcover huv)
    apply boundaryHub_route (kept : Set (Sym2 V)) zoneVertices component H hHB R root
      ?_ ?_ hselected
    · intro x y hxy hne
      exact SimpleGraph.Adj.reachable
        ⟨Finset.mem_union_left _ (Finset.mem_union_left _ hxy), hne⟩
    · intro x q hxq
      apply (hspokes x q hxq).mono
      intro a b hab
      refine ⟨?_, hab.2⟩
      rcases Finset.mem_union.mp hab.1 with hs | ha
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hs)
      · exact Finset.mem_union_right _ ha

end OnlineSteinerForest.UpperBound
