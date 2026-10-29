import OnlineSteinerForest.Graph.ResidualBounds
import OnlineSteinerForest.Graph.Comparison

/-! The residual distance used by the implementation satisfies the path-metric laws. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem IsPathEdges.reverse {G : SimpleGraph V} {s t : V} {F : Finset (Sym2 V)}
    (h : IsPathEdges G s t F) : IsPathEdges G t s F := by
  obtain ⟨p, hp, rfl⟩ := h
  exact ⟨p.reverse, hp.reverse, by simp⟩

theorem residualDistance_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) :
    0 ≤ residualDistance G c B s t h := by
  have hpath := (shortestPathEdges_spec G c B s t h).1
  exact residualCost_nonneg c B _ (fun e he => hc e (hpath.subset_edgeSet e he))

theorem residualDistance_symm (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) :
    residualDistance G c B s t h = residualDistance G c B t s h.symm := by
  apply le_antisymm
  · exact (shortestPathEdges_spec G c B s t h).2 _
      (shortestPathEdges_spec G c B t s h.symm).1.reverse
  · exact (shortestPathEdges_spec G c B t s h.symm).2 _
      (shortestPathEdges_spec G c B s t h).1.reverse

theorem residualDistance_triangle (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V)) (s u t : V)
    (hsu : G.Reachable s u) (hut : G.Reachable u t) :
    residualDistance G c B s t (hsu.trans hut) ≤
      residualDistance G c B s u hsu + residualDistance G c B u t hut := by
  let P := shortestPathEdges G c B s u hsu
  let Q := shortestPathEdges G c B u t hut
  obtain ⟨p, hp, heP⟩ := (shortestPathEdges_spec G c B s u hsu).1
  obtain ⟨q, hq, heQ⟩ := (shortestPathEdges_spec G c B u t hut).1
  let r := (p.append q).toPath
  have hr : IsPathEdges G s t r.val.edges.toFinset := ⟨r.val, r.prop, rfl⟩
  have hsub : r.val.edges.toFinset ⊆ P ∪ Q := by
    intro e he
    have he' := (p.append q).edges_toPath_subset_edges (List.mem_toFinset.mp he)
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he'
    simpa only [P, Q, ← heP, ← heQ, Finset.mem_union, List.mem_toFinset] using he'
  have hnonneg : ∀ e ∈ P ∪ Q, 0 ≤ c e := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hc e ((shortestPathEdges_spec G c B s u hsu).1.subset_edgeSet e he)
    · exact hc e ((shortestPathEdges_spec G c B u t hut).1.subset_edgeSet e he)
  calc
    _ ≤ residualCost c B r.val.edges.toFinset :=
      (shortestPathEdges_spec G c B s t (hsu.trans hut)).2 _ hr
    _ ≤ residualCost c B (P ∪ Q) := residualCost_mono_edges c B _ _ hsub hnonneg
    _ ≤ residualCost c B P + residualCost c B Q :=
      residualCost_union_le c B P Q (fun e he => hnonneg e (Finset.mem_union_right _ he))
    _ = _ := rfl

/-- Every connection already present among purchased edges has residual distance zero. -/
theorem residualDistance_eq_zero_of_bought (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) (s t : V) (h : G.Reachable s t)
    (hb : (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable s t) :
    residualDistance G c B s t h = 0 := by
  obtain ⟨P, hP, hPB⟩ := exists_pathEdges_subset hB hb
  apply le_antisymm
  · have hmin := (shortestPathEdges_spec G c B s t h).2 P hP
    simpa only [residualDistance, residualCost_eq_zero_of_subset c B P hPB] using hmin
  · exact residualDistance_nonneg G c hc B s t h

end OnlineSteinerForest
