import OnlineSteinerForest.UpperBound.ZonesComponentCounts
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A finite forest has at most as many edges as vertices, component by component. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

theorem forest_edge_count_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsAcyclic) : G.edgeFinset.card ≤ Fintype.card V := by
  let components := Finset.univ.image G.connectedComponentMk
  let edges (C : G.ConnectedComponent) : Finset (Sym2 V) :=
    C.toSimpleGraph.edgeFinset.map (Function.Embedding.subtype C.supp).sym2Map
  have hsub : G.edgeFinset ⊆ components.biUnion edges := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
      let C := G.connectedComponentMk u
      have hu : u ∈ C.supp := (C.mem_supp_iff u).mpr rfl
      have hv : v ∈ C.supp := (C.mem_supp_iff v).mpr
        (SimpleGraph.ConnectedComponent.sound huv.reachable).symm
      apply Finset.mem_biUnion.mpr
      refine ⟨C, Finset.mem_image_of_mem _ (Finset.mem_univ u), ?_⟩
      apply Finset.mem_map.mpr
      exact ⟨s((⟨u, hu⟩ : C), (⟨v, hv⟩ : C)), SimpleGraph.mem_edgeFinset.mpr huv, rfl⟩
  have hsum : (∑ C ∈ components, Fintype.card C) = Fintype.card V := by
    have h := sum_componentTerminals G Finset.univ
    simpa only [componentTerminals, Finset.mem_univ, Finset.filter_true,
      Finset.card_univ] using h
  calc
    G.edgeFinset.card ≤ (components.biUnion edges).card := Finset.card_le_card hsub
    _ ≤ ∑ C ∈ components, (edges C).card := Finset.card_biUnion_le
    _ ≤ ∑ C ∈ components, Fintype.card C := by
      apply Finset.sum_le_sum
      intro C _
      have hc := (hG.isTree_connectedComponent C).card_edgeFinset
      simpa only [edges, Finset.card_map] using (show C.toSimpleGraph.edgeFinset.card ≤
        Fintype.card C by omega)
    _ = Fintype.card V := hsum

end OnlineSteinerForest.UpperBound
