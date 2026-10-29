import OnlineSteinerForest.UpperBound.ZonesTreeLeafEdges

/-! Every standard finite tree has an edge-disjoint rooted branch expression. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
universe u

theorem exists_zoneTree {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (r : V) :
    ∃ t : ZoneTree V r, t.Valid ∧ t.edges = G.edgeFinset ∧ t.vertices = Finset.univ := by
  have aux : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (hH : H.IsTree) (r : W), Fintype.card W = n →
      ∃ t : ZoneTree W r, t.Valid ∧ t.edges = H.edgeFinset ∧ t.vertices = Finset.univ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hH r hn
      by_cases hnt : Nontrivial W
      · let _ := hnt
        obtain ⟨a, b, hab, ha, hb⟩ := hH.exists_ne_and_degree_eq_one
        obtain ⟨v, hvr, hv⟩ : ∃ v : W, v ≠ r ∧ H.degree v = 1 := by
          by_cases har : a = r
          · exact ⟨b, fun hbr => hab (har.trans hbr.symm), hb⟩
          · exact ⟨a, har, ha⟩
        obtain ⟨u, hvu, hu⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
        let S : Set W := {v}ᶜ
        let H' := H.induce S
        have hrS : r ∈ S := by simpa [S] using Ne.symm hvr
        have huS : u ∈ S := by simpa [S] using hvu.ne.symm
        have hH' : H'.IsTree :=
          ⟨hH.connected.induce_compl_singleton_of_degree_eq_one hv, hH.isAcyclic.induce S⟩
        have hcard : Fintype.card ↥S < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp [S])
        obtain ⟨t', ht', he', hv'⟩ := ih _ hcard ↥S H' hH' ⟨r, hrS⟩ rfl
        let t : ZoneTree W r := t'.map Subtype.val
        have htv : t.vertices = Finset.univ.erase v := by
          ext w
          simp [t, hv', S]
        have huT : u ∈ t.vertices := by rw [htv]; simp [hvu.ne.symm]
        have hvT : v ∉ t.vertices := by rw [htv]; simp
        refine ⟨t.graft u v huT, t.valid_graft (t'.valid_map ht' _ Subtype.val_injective) u v huT hvT, ?_, ?_⟩
        · rw [ZoneTree.edges_graft]
          change insert s(u, v) (t'.map Subtype.val).edges = _
          rw [ZoneTree.edges_map, he']
          exact tree_leaf_edges H u v hvu hu
        · rw [ZoneTree.vertices_graft, htv, Finset.insert_erase (Finset.mem_univ v)]
      · have : Subsingleton W := not_nontrivial_iff_subsingleton.mp hnt
        refine ⟨.leaf r, trivial, ?_, ?_⟩
        · ext e
          refine Sym2.ind (fun a b => ?_) e
          simp [ZoneTree.edges, SimpleGraph.mem_edgeFinset,
            show a = b from Subsingleton.elim _ _]
        · ext w
          simp [ZoneTree.vertices, show w = r from Subsingleton.elim _ _]
  exact aux (Fintype.card V) V G hG r rfl

end OnlineSteinerForest.UpperBound
