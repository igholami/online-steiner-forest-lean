import OnlineSteinerForest.UpperBound.ZonesSpokeAttachment
import OnlineSteinerForest.UpperBound.ZonesSpokeCount
import OnlineSteinerForest.UpperBound.ZonesAttachmentUnion

/-! Simultaneously restoring every selected hub-tree spoke at the incidence budget. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V I C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

theorem exists_hub_attachments (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (outside : Set (Sym2 V))
    (zones : I → Finset (Sym2 V)) (zoneVertices : I → Set V) (component : I → C)
    (anchor : I → V) (root : C → V) (skeleton : Finset (Sym2 V))
    (budget : ℝ) (hbudget : 0 ≤ budget)
    (hinput : ∀ i, ∀ e ∈ zones i, e ∈ G.edgeSet)
    (hzone : ∀ i v, v ∈ zoneVertices i →
      (SimpleGraph.fromEdgeSet (zones i : Set (Sym2 V))).Reachable v (anchor i))
    (hcost : ∀ i, edgeCost c (zones i) ≤ budget)
    (hskel : ∀ i, (SimpleGraph.fromEdgeSet (skeleton : Set (Sym2 V))).Reachable
      (anchor i) (root (component i)))
    (H : SimpleGraph (V ⊕ C)) (hH : H ≤ boundaryHubGraph outside zoneVertices component) :
    ∃ A : Finset (Sym2 V), (∀ e ∈ A, e ∈ G.edgeSet) ∧
      edgeCost c A ≤ (∑ q : C, (H.degree (.inr q) : ℝ)) * budget ∧
      ∀ (v : V) (q : C), H.Adj (.inl v) (.inr q) →
        (SimpleGraph.fromEdgeSet ((skeleton ∪ A : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
          v (root q) := by
  let J := ↥(hubSpokes H)
  have hlocal : ∀ p : J, ∃ P : Finset (Sym2 V), (∀ e ∈ P, e ∈ G.edgeSet) ∧
      edgeCost c P ≤ budget ∧
      (SimpleGraph.fromEdgeSet ((skeleton ∪ P : Finset (Sym2 V)) : Set (Sym2 V))).Reachable
        p.val.1 (root p.val.2) := by
    intro p
    exact exists_spoke_attachment G c hc outside zones zoneVertices component anchor root
      skeleton budget hinput hzone hcost hskel (hH (Finset.mem_filter.mp p.property).2)
  obtain ⟨A, hA, hcostA, hreach⟩ := exists_attachment_union G c hc skeleton
    (fun p : J => p.val.1) (fun p : J => root p.val.2) budget hlocal
  refine ⟨A, hA, hcostA.trans ?_, ?_⟩
  · apply mul_le_mul_of_nonneg_right _ hbudget
    have h := hubSpokes_card_le H
    simpa only [J, Fintype.card_coe, Nat.cast_sum] using (Nat.cast_le (α := ℝ)).mpr h
  · intro v q hvq
    exact hreach ⟨(v, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvq⟩⟩

end OnlineSteinerForest.UpperBound
