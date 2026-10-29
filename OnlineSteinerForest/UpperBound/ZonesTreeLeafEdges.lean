import OnlineSteinerForest.UpperBound.ZonesTreeValid
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Exact edge partition after removing a leaf of a standard finite tree. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem tree_leaf_edges (G : SimpleGraph V) (u v : V) (huv : G.Adj v u)
    (hunique : ∀ w, G.Adj v w → w = u) :
    insert s(u, v) ((G.induce ({v}ᶜ : Set V)).edgeFinset.image (Sym2.map Subtype.val)) =
      G.edgeFinset := by
  ext e
  constructor
  · intro he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact G.mem_edgeFinset.mpr huv.symm
    · obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp he
      rw [← hae]
      have hmap : ∀ x : Sym2 ↥({v}ᶜ : Set V), x ∈ (G.induce ({v}ᶜ : Set V)).edgeSet →
          Sym2.map Subtype.val x ∈ G.edgeSet := by
        intro x
        refine Sym2.ind (fun a b hab => ?_) x
        exact hab
      exact G.mem_edgeFinset.mpr (hmap a ((G.induce ({v}ᶜ : Set V)).mem_edgeFinset.mp ha))
  · refine Sym2.ind (fun a b hab => ?_) e
    have hab' : G.Adj a b := G.mem_edgeFinset.mp hab
    by_cases ha : a = v
    · subst a
      have hb := hunique b hab'
      subst b
      exact Finset.mem_insert.mpr (Or.inl (Sym2.eq_swap))
    by_cases hb : b = v
    · subst b
      have ha := hunique a hab'.symm
      subst a
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, rfl⟩
      exact (G.induce ({v}ᶜ : Set V)).mem_edgeFinset.mpr hab'

end OnlineSteinerForest.UpperBound
