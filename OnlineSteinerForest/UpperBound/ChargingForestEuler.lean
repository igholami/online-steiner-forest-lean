import OnlineSteinerForest.UpperBound.ZonesForestCard

/-! Exact Euler accounting for an ordinary finite forest, including isolated vertices. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

theorem forest_euler {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) :
    G.edgeFinset.card + Nat.card G.ConnectedComponent = Fintype.card V := by
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  let components := Finset.univ.image G.connectedComponentMk
  let edges (C : G.ConnectedComponent) : Finset (Sym2 V) :=
    C.toSimpleGraph.edgeFinset.map (Function.Embedding.subtype C.supp).sym2Map
  have hmem : ∀ C e, e ∈ edges C → ∀ v ∈ e, v ∈ C.supp := by
    intro C e he
    obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp he
    rw [← hfe]
    refine Sym2.ind (fun a b v hv => ?_) f
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact a.property
    · exact b.property
  have hd : ∀ C ∈ components, ∀ D ∈ components, C ≠ D → Disjoint (edges C) (edges D) := by
    intro C hC D hD hne
    apply Finset.disjoint_left.mpr
    intro e heC heD
    have hc := (C.mem_supp_iff e.out.1).mp (hmem C e heC _ (Sym2.out_fst_mem e))
    have hd := (D.mem_supp_iff e.out.1).mp (hmem D e heD _ (Sym2.out_fst_mem e))
    exact hne (hc.symm.trans hd)
  have heq : components.biUnion edges = G.edgeFinset := by
    ext e
    constructor
    · intro he
      obtain ⟨C, hC, heC⟩ := Finset.mem_biUnion.mp he
      obtain ⟨f, hf, hfe⟩ := Finset.mem_map.mp heC
      rw [← hfe]
      have hmap : ∀ f : Sym2 C, f ∈ C.toSimpleGraph.edgeSet →
          Sym2.map Subtype.val f ∈ G.edgeSet := by
        intro f
        refine Sym2.ind (fun a b hab => ?_) f
        exact hab
      exact G.mem_edgeFinset.mpr (hmap f (C.toSimpleGraph.mem_edgeFinset.mp hf))
    · refine Sym2.ind (fun u v huv => ?_) e
      have huv' : G.Adj u v := G.mem_edgeFinset.mp huv
      let C := G.connectedComponentMk u
      have hu : u ∈ C.supp := (C.mem_supp_iff u).mpr rfl
      have hv : v ∈ C.supp := (C.mem_supp_iff v).mpr
        (SimpleGraph.ConnectedComponent.sound huv'.reachable).symm
      exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_image_of_mem _ (Finset.mem_univ u),
        Finset.mem_map.mpr ⟨s((⟨u, hu⟩ : C), (⟨v, hv⟩ : C)),
          C.toSimpleGraph.mem_edgeFinset.mpr huv', rfl⟩⟩
  have hsum : (∑ C ∈ components, Fintype.card C) = Fintype.card V := by
    have h := sum_componentTerminals G Finset.univ
    simpa only [componentTerminals, Finset.mem_univ, Finset.filter_true, Finset.card_univ] using h
  have hcomp : components = Finset.univ := by
    ext C
    simp only [components, Finset.mem_image, Finset.mem_univ, true_and, iff_true]
    induction C using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, rfl⟩
  have hcard : components.card = Nat.card G.ConnectedComponent := by
    simp only [hcomp, Finset.card_univ, Nat.card_eq_fintype_card]
  calc
    _ = (∑ C ∈ components, (edges C).card) + components.card := by
      rw [← heq, Finset.card_biUnion hd, hcard]
    _ = ∑ C ∈ components, ((edges C).card + 1) := by simp [Finset.sum_add_distrib]
    _ = ∑ C ∈ components, Fintype.card C := by
      apply Finset.sum_congr rfl
      intro C hC
      simpa only [edges, Finset.card_map] using (hG.isTree_connectedComponent C).card_edgeFinset
    _ = _ := hsum

end OnlineSteinerForest.UpperBound
