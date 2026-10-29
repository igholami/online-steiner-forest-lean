import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Original ambient edge sets of ordinary reference connected components. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def componentEdges (G : SimpleGraph V) (C : G.ConnectedComponent) : Finset (Sym2 V) :=
  C.toSimpleGraph.edgeFinset.map (Function.Embedding.subtype C.supp).sym2Map

theorem mem_componentEdges (G : SimpleGraph V) (C : G.ConnectedComponent) (u v : V) :
    s(u, v) ∈ componentEdges G C ↔ G.Adj u v ∧ G.connectedComponentMk u = C := by
  let e : C ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
  change s(u, v) ∈ C.toSimpleGraph.edgeFinset.map e.sym2Map ↔ _
  rw [← SimpleGraph.edgeFinset_map, SimpleGraph.mem_edgeFinset]
  change (C.toSimpleGraph.map e).Adj u v ↔ _
  rw [SimpleGraph.map_adj]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    subst u
    subst v
    exact ⟨hab, (C.mem_supp_iff a.val).mp a.property⟩
  · rintro ⟨huv, hu⟩
    have huC : u ∈ C.supp := (C.mem_supp_iff u).mpr hu
    have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp huC huv
    exact ⟨⟨u, huC⟩, ⟨v, hvC⟩, huv, rfl, rfl⟩

theorem componentEdges_subset (G : SimpleGraph V) (C : G.ConnectedComponent) :
    componentEdges G C ⊆ G.edgeFinset := by
  intro e he
  induction e using Sym2.ind with
  | _ u v => exact SimpleGraph.mem_edgeFinset.mpr ((mem_componentEdges G C u v).mp he).1

end OnlineSteinerForest.UpperBound
