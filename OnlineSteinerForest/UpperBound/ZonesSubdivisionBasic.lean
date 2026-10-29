import OnlineSteinerForest.UpperBound.ZonesTreeValid
import Mathlib.Tactic.Ring

/-! One subdivision inserts a private midpoint into each original edge. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [DecidableEq V]

abbrev ZoneSubdivisionVertex (V : Type*) := V ⊕ Sym2 V

def zoneSplitEdges (e : Sym2 V) : Finset (Sym2 (ZoneSubdivisionVertex V)) :=
  e.toFinset.image (fun v => s(Sum.inl v, Sum.inr e))

@[simp] theorem zoneSplitEdges_mk (u v : V) : zoneSplitEdges s(u, v) =
    {s(Sum.inl u, Sum.inr s(u, v)), s(Sum.inr s(u, v), Sum.inl v)} := by
  simp [zoneSplitEdges, Sym2.toFinset_mk_eq, Sym2.eq_swap]

theorem zoneSplitEdges_disjoint {e f : Sym2 V} (hne : e ≠ f) :
    Disjoint (zoneSplitEdges e) (zoneSplitEdges f) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp hx
  obtain ⟨v, hv, hfq⟩ := Finset.mem_image.mp hy
  have h := heq.trans hfq.symm
  rcases Sym2.eq_iff.mp h with h | h
  · exact hne (Sum.inr.inj h.2)
  · cases h.1

noncomputable def zoneHalfCost (c : Sym2 V → ℝ) : Sym2 (ZoneSubdivisionVertex V) → ℝ :=
  Sym2.lift ⟨(fun x y => match x, y with
    | .inl _, .inr e => c e / 2
    | .inr e, .inl _ => c e / 2
    | _, _ => 0), by intro x y; cases x <;> cases y <;> rfl⟩

@[simp] theorem zoneHalfCost_left (c : Sym2 V → ℝ) (v : V) (e : Sym2 V) :
    zoneHalfCost c s(Sum.inl v, Sum.inr e) = c e / 2 := rfl

@[simp] theorem zoneHalfCost_right (c : Sym2 V → ℝ) (v : V) (e : Sym2 V) :
    zoneHalfCost c s(Sum.inr e, Sum.inl v) = c e / 2 := rfl

theorem zoneSplitEdges_cost (c : Sym2 V → ℝ) (e : Sym2 V) (he : ¬e.IsDiag) :
    edgeCost (zoneHalfCost c) (zoneSplitEdges e) = c e := by
  refine Sym2.ind (fun u v huv => ?_) e he
  have hne : u ≠ v := by simpa [Sym2.mk_isDiag_iff] using huv
  have hn : s(Sum.inl u, Sum.inr s(u, v)) ≠ s(Sum.inr s(u, v), Sum.inl v) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · cases h.1
    · exact hne (Sum.inl.inj h.1)
  rw [zoneSplitEdges_mk, edgeCost, Finset.sum_pair hn]
  simp only [zoneHalfCost_left, zoneHalfCost_right]
  ring

namespace ZoneTree

def subdivide {r : V} : ZoneTree V r → ZoneTree (ZoneSubdivisionVertex V) (Sum.inl r)
  | .leaf r => .leaf (Sum.inl r)
  | .extend r s t => .extend (Sum.inl r) (Sum.inr s(r, s))
      (.extend (Sum.inr s(r, s)) (Sum.inl s) t.subdivide)
  | .join r a b => .join (Sum.inl r) a.subdivide b.subdivide

@[simp] theorem edges_subdivide {r : V} (t : ZoneTree V r) :
    t.subdivide.edges = t.edges.biUnion zoneSplitEdges := by
  induction t with
  | leaf => simp [subdivide, edges]
  | extend r s t ih => simp [subdivide, edges, ih, Finset.biUnion_insert,
      zoneSplitEdges_mk, Finset.insert_union]
  | join r a b ha hb =>
    simp only [subdivide, edges, ha, hb]
    ext x
    simp [Finset.mem_biUnion, or_and_right, exists_or]

end ZoneTree
end OnlineSteinerForest.UpperBound
