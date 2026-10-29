import OnlineSteinerForest.UpperBound.AuxiliaryAfterStep

/-! A purchased path merges exactly the old components that its support touches. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [DecidableEq V]

/-- A walk in the union cannot leave an old component that avoids the new path. -/
theorem reachable_union_of_avoids_path {G : SimpleGraph V} {s t a : V}
    (B : Finset (Sym2 V)) (p : G.Walk s t)
    (havoid : ∀ w ∈ p.support, ¬ (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable a w)
    {u v : V} (q : (SimpleGraph.fromEdgeSet ((B ∪ p.edges.toFinset : Finset _) : Set (Sym2 V))).Walk u v)
    (hau : (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable a u) :
    (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable a v := by
  induction q with
  | nil => exact hau
  | @cons u b v hab q ih =>
    apply ih
    have heh : s(u, b) ∈ B ∪ p.edges.toFinset ∧ u ≠ b := by
      simpa only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe] using hab
    obtain ⟨he, hne⟩ := heh
    rcases Finset.mem_union.mp he with he | he
    · exact hau.trans (SimpleGraph.Adj.reachable (by simpa only [SimpleGraph.fromEdgeSet_adj, Finset.mem_coe] using (And.intro he hne)))
    · exact False.elim (havoid u (p.fst_mem_support_of_mem_edges (List.mem_toFinset.mp he)) hau)

/-- Reachability to the new path's source detects exactly the old touched components. -/
theorem reachable_union_source_iff_touches {G : SimpleGraph V} {s t a : V}
    (B : Finset (Sym2 V)) (p : G.Walk s t) :
    (SimpleGraph.fromEdgeSet ((B ∪ p.edges.toFinset : Finset _) : Set (Sym2 V))).Reachable a s ↔
      ∃ w ∈ p.support, (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable a w := by
  classical
  constructor
  · intro h
    by_contra hn
    have havoid : ∀ w ∈ p.support,
        ¬ (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable a w := by
      simpa only [not_exists, not_and] using hn
    obtain ⟨q⟩ := h
    exact havoid s p.start_mem_support (reachable_union_of_avoids_path B p havoid q (.refl _))
  · rintro ⟨w, hw, haw⟩
    have h1 := reachable_mono_edges (Finset.subset_union_left : B ⊆ B ∪ p.edges.toFinset) haw
    have h2 := reachable_mono_edges (Finset.subset_union_right : p.edges.toFinset ⊆ B ∪ p.edges.toFinset)
      (walk_support_reachable p w hw)
    exact h1.trans h2.symm

/-- Components not merged with the request component retain exactly their old reachability. -/
theorem reachable_union_iff_of_untouched {G : SimpleGraph V} {s t a v : V}
    (B : Finset (Sym2 V)) (p : G.Walk s t)
    (hnot : ¬ (SimpleGraph.fromEdgeSet ((B ∪ p.edges.toFinset : Finset _) : Set (Sym2 V))).Reachable a s) :
    (SimpleGraph.fromEdgeSet ((B ∪ p.edges.toFinset : Finset _) : Set (Sym2 V))).Reachable a v ↔
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable a v := by
  constructor
  · rintro ⟨q⟩
    apply reachable_union_of_avoids_path B p _ q (.refl _)
    intro w hw haw
    exact hnot ((reachable_union_source_iff_touches B p).mpr ⟨w, hw, haw⟩)
  · exact reachable_mono_edges Finset.subset_union_left

end OnlineSteinerForest.UpperBound
