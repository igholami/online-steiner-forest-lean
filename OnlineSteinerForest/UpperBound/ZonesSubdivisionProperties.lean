import OnlineSteinerForest.UpperBound.ZonesSubdivisionBasic

/-! Subdivision preserves edge disjointness and total cost and halves edge weights. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [DecidableEq V]

theorem zoneSplitUnion_disjoint {E F : Finset (Sym2 V)} (hEF : Disjoint E F) :
    Disjoint (E.biUnion zoneSplitEdges) (F.biUnion zoneSplitEdges) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨f, hf, hxf⟩ := Finset.mem_biUnion.mp hy
  have hne : e ≠ f := fun h => Finset.disjoint_left.mp hEF he (h ▸ hf)
  exact Finset.disjoint_left.mp (zoneSplitEdges_disjoint hne) hxe hxf

theorem zoneSplitUnion_cost (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hE : ∀ e ∈ E, ¬e.IsDiag) :
    edgeCost (zoneHalfCost c) (E.biUnion zoneSplitEdges) = edgeCost c E := by
  rw [edgeCost, Finset.sum_biUnion (fun e _ f _ hef => zoneSplitEdges_disjoint hef)]
  exact Finset.sum_congr rfl (fun e he => zoneSplitEdges_cost c e (hE e he))

theorem zoneSplitUnion_edge {E : Finset (Sym2 V)} {x : Sym2 (ZoneSubdivisionVertex V)}
    (hx : x ∈ E.biUnion zoneSplitEdges) : ∃ e ∈ E, ¬x.IsDiag ∧ ∀ c : Sym2 V → ℝ,
      zoneHalfCost c x = c e / 2 := by
  obtain ⟨e, he, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨e, he, by simp [Sym2.mk_isDiag_iff], fun _ => rfl⟩

namespace ZoneTree

theorem valid_subdivide {r : V} (t : ZoneTree V r) (ht : t.Valid)
    (hnd : ∀ e ∈ t.edges, ¬e.IsDiag) : t.subdivide.Valid := by
  induction t with
  | leaf => trivial
  | extend r s t ih =>
    have hneq : r ≠ s := by simpa only [Sym2.mk_isDiag_iff] using hnd s(r, s) (Finset.mem_insert_self _ _)
    have hnd' : ∀ e ∈ t.edges, ¬e.IsDiag := fun e he => hnd e (Finset.mem_insert_of_mem he)
    have hd : Disjoint (zoneSplitEdges s(r, s)) t.subdivide.edges := by
      rw [edges_subdivide]
      simpa only [Finset.singleton_biUnion] using zoneSplitUnion_disjoint
        (show Disjoint {s(r, s)} t.edges by simpa using ht.1)
    have hfirst : s(Sum.inl r, Sum.inr s(r, s)) ∈ zoneSplitEdges s(r, s) := by simp
    have hsecond : s(Sum.inr s(r, s), Sum.inl s) ∈ zoneSplitEdges s(r, s) := by simp
    have hpair : s(Sum.inl r, Sum.inr s(r, s)) ≠ s(Sum.inr s(r, s), Sum.inl s) := by
      intro he
      rcases Sym2.eq_iff.mp he with he | he
      · cases he.1
      · exact hneq (Sum.inl.inj he.1)
    change _ ∧ _ ∧ _
    refine ⟨?_, ?_, ih ht.2 hnd'⟩
    · intro he
      rcases Finset.mem_insert.mp he with he | he
      · exact hpair he
      · exact Finset.disjoint_left.mp hd hfirst he
    · exact fun he => Finset.disjoint_left.mp hd hsecond he
  | join r a b ha hb =>
    change Disjoint _ _ ∧ _ ∧ _
    rw [edges_subdivide, edges_subdivide]
    exact ⟨zoneSplitUnion_disjoint ht.1,
      ha ht.2.1 (fun e he => hnd e (Finset.mem_union_left _ he)),
      hb ht.2.2 (fun e he => hnd e (Finset.mem_union_right _ he))⟩

end ZoneTree
end OnlineSteinerForest.UpperBound
