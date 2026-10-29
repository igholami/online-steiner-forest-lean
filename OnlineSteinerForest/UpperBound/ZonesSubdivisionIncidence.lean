import OnlineSteinerForest.UpperBound.ZonesSubdivisionProperties

/-! The subdivided graph is exactly the incidence graph of the original edges. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {V : Type*} [DecidableEq V]

@[simp] theorem mem_split_incidence (E : Finset (Sym2 V)) (v : V) (e : Sym2 V) :
    s(Sum.inl v, Sum.inr e) ∈ E.biUnion zoneSplitEdges ↔ e ∈ E ∧ v ∈ e := by
  simp [zoneSplitEdges, Finset.mem_biUnion, Sym2.eq_iff, Sym2.mem_toFinset, and_comm, and_left_comm]

@[simp] theorem not_mem_split_old (E : Finset (Sym2 V)) (u v : V) :
    s(Sum.inl u, Sum.inl v) ∉ E.biUnion zoneSplitEdges := by
  simp [zoneSplitEdges, Finset.mem_biUnion, Sym2.eq_iff]

@[simp] theorem not_mem_split_private (E : Finset (Sym2 V)) (e f : Sym2 V) :
    s(Sum.inr e, Sum.inr f) ∉ E.biUnion zoneSplitEdges := by
  simp [zoneSplitEdges, Finset.mem_biUnion, Sym2.eq_iff]

noncomputable def zoneRecombine (E : Finset (Sym2 V))
    (F : Finset (Sym2 (ZoneSubdivisionVertex V))) : Finset (Sym2 V) :=
  E.filter (fun e => zoneSplitEdges e ⊆ F)

theorem zoneRecombine_adj {E : Finset (Sym2 V)} {F : Finset (Sym2 (ZoneSubdivisionVertex V))}
    (hF : F ⊆ E.biUnion zoneSplitEdges) {u v : V} {e : Sym2 V}
    (hu : s(Sum.inl u, Sum.inr e) ∈ F) (hv : s(Sum.inl v, Sum.inr e) ∈ F) (hne : u ≠ v) :
    (SimpleGraph.fromEdgeSet (zoneRecombine E F : Set (Sym2 V))).Adj u v := by
  obtain ⟨he, hue⟩ := (mem_split_incidence E u e).mp (hF hu)
  obtain ⟨_, hve⟩ := (mem_split_incidence E v e).mp (hF hv)
  have heq : e = s(u, v) := (Sym2.mem_and_mem_iff hne).mp ⟨hue, hve⟩
  subst e
  refine ⟨Finset.mem_filter.mpr ⟨he, ?_⟩, hne⟩
  rw [zoneSplitEdges_mk]
  intro x hx
  rcases Finset.mem_insert.mp hx with rfl | hx
  · exact hu
  · have hx' : x = s(Sum.inr s(u, v), Sum.inl v) := Finset.mem_singleton.mp hx
    subst x
    simpa only [Sym2.eq_swap] using hv

theorem zoneRecombine_cost (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ E, 0 ≤ c e) (hnd : ∀ e ∈ E, ¬e.IsDiag)
    (F : Finset (Sym2 (ZoneSubdivisionVertex V))) (hF : F ⊆ E.biUnion zoneSplitEdges) :
    edgeCost c (zoneRecombine E F) ≤ edgeCost (zoneHalfCost c) F := by
  have hsub : (zoneRecombine E F).biUnion zoneSplitEdges ⊆ F := by
    intro x hx
    obtain ⟨e, he, hxe⟩ := Finset.mem_biUnion.mp hx
    exact (Finset.mem_filter.mp he).2 hxe
  rw [← zoneSplitUnion_cost (zoneRecombine E F) c
    (fun e he => hnd e (Finset.mem_filter.mp he).1)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x hx _ => by
    obtain ⟨e, he, _, hweight⟩ := zoneSplitUnion_edge (hF hx)
    rw [hweight]
    exact div_nonneg (hc e he) (by norm_num))

end OnlineSteinerForest.UpperBound
