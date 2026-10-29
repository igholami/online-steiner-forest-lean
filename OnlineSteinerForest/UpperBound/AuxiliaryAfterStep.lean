import OnlineSteinerForest.UpperBound.HistoryExecution

/-! A touched bought component is connected to both new request endpoints after the update. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem walk_support_reachable {G : SimpleGraph V} {s t : V} (p : G.Walk s t)
    (w : V) (hw : w ∈ p.support) :
    (SimpleGraph.fromEdgeSet (p.edges.toFinset : Set (Sym2 V))).Reachable s w := by
  exact walk_reachable_fromEdgeSet (p.takeUntil w hw) _
    (fun e he => List.mem_toFinset.mpr (p.edges_takeUntil_subset_edges hw he))

/-- If an old component is touched by the purchased path, every vertex of that
component joins both request endpoints in the actual updated purchased graph. -/
theorem greedyStep_connects_old_component (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (hst : G.Reachable s t) (C : Finset V)
    (hCC : ∀ u ∈ C, ∀ v ∈ C,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v)
    (p : G.Walk s t) (heq : p.edges.toFinset = shortestPathEdges G c B s t hst)
    (htouch : ∃ w ∈ C, w ∈ p.support) :
    ∀ v ∈ C, (SimpleGraph.fromEdgeSet (greedyStep G c B s t hst : Set (Sym2 V))).Reachable s v ∧
      (SimpleGraph.fromEdgeSet (greedyStep G c B s t hst : Set (Sym2 V))).Reachable t v := by
  obtain ⟨w, hwC, hwp⟩ := htouch
  have hPsub : p.edges.toFinset ⊆ greedyStep G c B s t hst := by
    rw [heq]
    exact Finset.subset_union_right
  have hsw := reachable_mono_edges hPsub (walk_support_reachable p w hwp)
  have hstP := walk_reachable_fromEdgeSet p p.edges.toFinset (by simp)
  have htw := reachable_mono_edges hPsub (hstP.symm.trans (walk_support_reachable p w hwp))
  intro v hv
  have hwv := reachable_mono_edges (greedyStep_mono G c B s t hst) (hCC w hwC v hv)
  exact ⟨hsw.trans hwv, htw.trans hwv⟩

theorem greedyStep_residual_zero_to_component (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) (s t : V) (hst : G.Reachable s t)
    (C : Finset V) (hsC : ∀ v ∈ C, G.Reachable s v)
    (hCC : ∀ u ∈ C, ∀ v ∈ C,
      (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).Reachable u v)
    (p : G.Walk s t) (heq : p.edges.toFinset = shortestPathEdges G c B s t hst)
    (htouch : ∃ w ∈ C, w ∈ p.support) :
    ∀ (v : V) (hv : v ∈ C),
      residualDistance G c (greedyStep G c B s t hst) s v (hsC v hv) = 0 ∧
      residualDistance G c (greedyStep G c B s t hst) t v (hst.symm.trans (hsC v hv)) = 0 := by
  have hpath := (shortestPathEdges_spec G c B s t hst).1
  have hnext : ∀ e ∈ greedyStep G c B s t hst, e ∈ G.edgeSet := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hB e he
    · exact hpath.subset_edgeSet e he
  intro v hv
  obtain ⟨hs, ht⟩ := greedyStep_connects_old_component G c B s t hst C hCC p heq htouch v hv
  exact ⟨residualDistance_eq_zero_of_bought G c hc _ hnext s v _ hs,
    residualDistance_eq_zero_of_bought G c hc _ hnext t v _ ht⟩

end OnlineSteinerForest.UpperBound
