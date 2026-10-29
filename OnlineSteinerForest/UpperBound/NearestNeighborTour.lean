import OnlineSteinerForest.UpperBound.NearestNeighborWalkCost
import OnlineSteinerForest.UpperBound.NearestNeighborInducedCost

/-! A finite nonnegative-cost tree has a closed covering walk of cost at most twice its edge cost. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

universe u

/-- Construct the doubled-tree tour by removing a leaf and inserting its excursion.
The walk and all connectivity facts use standard mathlib graph definitions. -/
theorem exists_tree_tour {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) :
    ∃ (r : V) (p : G.Walk r r), (∀ v : V, v ∈ p.support) ∧
      walkCost c p ≤ 2 * edgeCost c G.edgeFinset := by
  classical
  have aux : ∀ n : ℕ, ∀ (W : Type u) [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) (hH : H.IsTree) (d : Sym2 W → ℝ)
      (hd : ∀ e ∈ H.edgeSet, 0 ≤ d e), Fintype.card W = n →
      ∃ (r : W) (p : H.Walk r r), (∀ v : W, v ∈ p.support) ∧
        walkCost d p ≤ 2 * graphCost H d := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ H hH d hd hn
      by_cases hnt : Nontrivial W
      · let _ := hnt
        obtain ⟨v, hv⟩ := hH.exists_vert_degree_one_of_nontrivial
        obtain ⟨u, hvu, _⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
        let S : Set W := {v}ᶜ
        let H' := H.induce S
        let d' : Sym2 ↥S → ℝ := fun e => d (Sym2.map Subtype.val e)
        have hH' : H'.IsTree :=
          ⟨hH.connected.induce_compl_singleton_of_degree_eq_one hv, hH.isAcyclic.induce S⟩
        have hd' : ∀ e ∈ H'.edgeSet, 0 ≤ d' e := by
          intro e
          refine Sym2.ind (fun a b hab => ?_) e
          exact hd s(a.val, b.val) hab
        have hcard : Fintype.card ↥S < n := by
          rw [← hn]
          exact Fintype.card_subtype_lt (x := v) (by simp [S])
        obtain ⟨r, p, hcover, hcost⟩ := ih _ hcard ↥S H' hH' d' hd' rfl
        let f : H' →g H := (SimpleGraph.Embedding.induce S).toHom
        let pG := p.map f
        have huS : u ∈ S := by simpa [S] using hvu.ne.symm
        have huP : u ∈ pG.support := by
          change u ∈ (p.map f).support
          rw [SimpleGraph.Walk.support_map]
          exact List.mem_map.mpr ⟨⟨u, huS⟩, hcover ⟨u, huS⟩, rfl⟩
        refine ⟨f r, leafExcursion pG huP hvu.symm, ?_, ?_⟩
        · intro w
          by_cases hw : w = v
          · subst w
            exact leaf_mem_leafExcursion_support pG huP hvu.symm
          · apply mem_leafExcursion_support pG huP hvu.symm
            change w ∈ (p.map f).support
            rw [SimpleGraph.Walk.support_map]
            exact List.mem_map.mpr ⟨⟨w, by simpa [S] using hw⟩,
              hcover ⟨w, by simpa [S] using hw⟩, rfl⟩
        · have hcostmap : walkCost d pG = walkCost d' p := walkCost_map d f p
          have hbudget := induced_cost_add_edge_le H d hd S u v (by simp [S]) hvu.symm
          change graphCost H' d' + d s(u, v) ≤ graphCost H d at hbudget
          rw [walkCost_leafExcursion, hcostmap]
          linarith only [hcost, hbudget]
      · have : Subsingleton W := not_nontrivial_iff_subsingleton.mp hnt
        let r : W := Classical.choice hH.nonempty
        refine ⟨r, SimpleGraph.Walk.nil, ?_, ?_⟩
        · intro v
          have hv : v = r := Subsingleton.elim _ _
          simp [hv]
        · simp only [walkCost_nil]
          exact mul_nonneg (by norm_num) (graphCost_nonneg H d hd)
  simpa only [graphCost_eq_edgeFinset] using aux (Fintype.card V) V G hG c hc rfl

end OnlineSteinerForest.UpperBound
