import OnlineSteinerForest.Graph.Feasibility
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Relabel vertices, edge sets and costs along an ordinary finite-type equivalence. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def edgeEquiv (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv x := by simp [Sym2.map_map, Sym2.map_id']
  right_inv x := by simp [Sym2.map_map, Sym2.map_id']

def relabelEdges (e : V ≃ W) (F : Finset (Sym2 V)) : Finset (Sym2 W) :=
  F.map (edgeEquiv e).toEmbedding

def relabelCost (e : V ≃ W) (c : Sym2 V → ℝ) : Sym2 W → ℝ := c ∘ (edgeEquiv e).symm

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem relabelEdges_empty (e : V ≃ W) : relabelEdges e ∅ = ∅ := rfl

@[simp] theorem relabelEdges_union (e : V ≃ W) (F B : Finset (Sym2 V)) :
    relabelEdges e (F ∪ B) = relabelEdges e F ∪ relabelEdges e B := Finset.map_union _ _

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem relabelEdges_symm (e : V ≃ W) (F : Finset (Sym2 W)) :
    relabelEdges e (relabelEdges e.symm F) = F := by
  rw [relabelEdges, relabelEdges, Finset.map_map]
  have he : (edgeEquiv e.symm).toEmbedding.trans (edgeEquiv e).toEmbedding = Function.Embedding.refl _ := by
    ext x
    simp [edgeEquiv, Sym2.map_map]
  rw [he, Finset.map_refl]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem edgeCost_relabel (e : V ≃ W) (c : Sym2 V → ℝ) (F : Finset (Sym2 V)) :
    edgeCost (relabelCost e c) (relabelEdges e F) = edgeCost c F := by
  simp [edgeCost, relabelEdges, relabelCost]

@[simp] theorem residualCost_relabel (e : V ≃ W) (c : Sym2 V → ℝ) (B F : Finset (Sym2 V)) :
    residualCost (relabelCost e c) (relabelEdges e B) (relabelEdges e F) = residualCost c B F := by
  simp [residualCost, relabelEdges, relabelCost, ← Finset.map_sdiff]

omit [DecidableEq V] [DecidableEq W] in
@[simp] theorem relabelCost_apply (e : V ≃ W) (c : Sym2 V → ℝ) (x : Sym2 V) :
    relabelCost e c (edgeEquiv e x) = c x := by simp [relabelCost]

/-- A standard simple path is preserved by a graph isomorphism. -/
theorem IsPathEdges.mapIso {G : SimpleGraph V} {H : SimpleGraph W}
    {s t : V} {F : Finset (Sym2 V)} (hp : IsPathEdges G s t F) (f : G ≃g H) :
    IsPathEdges H (f s) (f t) (relabelEdges f.toEquiv F) := by
  obtain ⟨p, hp, rfl⟩ := hp
  refine ⟨p.map f.toHom, hp.map f.injective, ?_⟩
  rw [SimpleGraph.Walk.edges_map]
  ext x
  simp only [List.mem_toFinset, List.mem_map, relabelEdges, Finset.mem_map, Equiv.toEmbedding_apply]
  constructor
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, hax⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨a, ha, hax⟩

end OnlineSteinerForest
