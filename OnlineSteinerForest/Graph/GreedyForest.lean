import OnlineSteinerForest.Greedy.Feasibility
import OnlineSteinerForest.Graph.ResidualBounds
import OnlineSteinerForest.Graph.Comparison
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.Linarith

/-! Strictly positive new edges of a residual shortest path are bridges.
Consequently the implemented greedy algorithm always purchases a forest. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem greedyStep_new_edge_isBridge (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet) (s t : V) (hst : G.Reachable s t)
    (e : Sym2 V) (he : e ∈ shortestPathEdges G c B s t hst) (heB : e ∉ B) :
    (SimpleGraph.fromEdgeSet (greedyStep G c B s t hst : Set (Sym2 V))).IsBridge e := by
  classical
  let P := shortestPathEdges G c B s t hst
  let H := SimpleGraph.fromEdgeSet ((B ∪ P : Finset (Sym2 V)) : Set (Sym2 V))
  let F := (B ∪ P).erase e
  have hP := (shortestPathEdges_spec G c B s t hst).1
  change H.IsBridge e
  by_contra hn
  have hconn : H.Reachable s t := reachable_mono_edges Finset.subset_union_right hP.reachable
  have hdelete := hconn.reachable_deleteEdges_of_not_isBridge hn
  have hgraphs : H.deleteEdges {e} = SimpleGraph.fromEdgeSet (F : Set (Sym2 V)) := by
    ext u v
    simp only [H, F, SimpleGraph.deleteEdges_adj, SimpleGraph.fromEdgeSet_adj,
      Set.mem_singleton_iff, Finset.mem_coe, Finset.mem_union, Finset.mem_erase]
    aesop
  rw [hgraphs] at hdelete
  have hF : ∀ a ∈ F, a ∈ G.edgeSet := by
    intro a ha
    rcases Finset.mem_union.mp (Finset.mem_erase.mp ha).2 with ha | ha
    · exact hB a ha
    · exact hP.subset_edgeSet a ha
  obtain ⟨Q, hQ, hQF⟩ := exists_pathEdges_subset hF hdelete
  have hmin := (shortestPathEdges_spec G c B s t hst).2 Q hQ
  have hbound : residualCost c B Q ≤ residualCost c B F :=
    residualCost_mono_edges c B Q F hQF (fun a ha => (hc a (hF a ha)).le)
  have hdiff : F \ B = (P \ B).erase e := by
    ext a
    simp only [F, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_union]
    aesop
  have hsum : residualCost c B F + c e = residualCost c B P := by
    unfold residualCost
    rw [hdiff]
    exact Finset.sum_erase_add _ _ (Finset.mem_sdiff.mpr ⟨he, heB⟩)
  have hpos := hc e (hP.subset_edgeSet e he)
  change residualCost c B P ≤ residualCost c B Q at hmin
  linarith

theorem greedyStep_isAcyclic (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet)
    (hforest : (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).IsAcyclic)
    (s t : V) (hst : G.Reachable s t) :
    (SimpleGraph.fromEdgeSet (greedyStep G c B s t hst : Set (Sym2 V))).IsAcyclic := by
  classical
  intro u p hp
  have htransfer : ∀ e ∈ p.edges, e ∈ (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).edgeSet := by
    intro e he
    have heG := p.edges_subset_edgeSet he
    have he' : e ∈ (greedyStep G c B s t hst : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa only [SimpleGraph.edgeSet_fromEdgeSet] using heG
    have heB : e ∈ B := by
      by_contra hn
      have heP : e ∈ shortestPathEdges G c B s t hst :=
        (Finset.mem_union.mp he'.1).resolve_left hn
      have hbridge := greedyStep_new_edge_isBridge G c hc B hB s t hst e heP hn
      exact hbridge.notMem_edges_of_isCycle hp he
    simpa only [SimpleGraph.edgeSet_fromEdgeSet] using
      (show e ∈ (B : Set (Sym2 V)) \ Sym2.diagSet from ⟨heB, he'.2⟩)
  exact hforest (p.transfer _ htransfer) (hp.transfer htransfer)

theorem greedy_isAcyclic_from (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (B : Finset (Sym2 V))
    (hB : ∀ e ∈ B, e ∈ G.edgeSet)
    (hforest : (SimpleGraph.fromEdgeSet (B : Set (Sym2 V))).IsAcyclic) :
    (SimpleGraph.fromEdgeSet (greedy G c requests feasible B : Set (Sym2 V))).IsAcyclic := by
  induction requests generalizing B with
  | nil => exact hforest
  | cons q qs ih =>
    have hpath := (shortestPathEdges_spec G c B q.1 q.2 (feasible q (by simp))).1
    have hnext : ∀ e ∈ greedyStep G c B q.1 q.2 (feasible q (by simp)), e ∈ G.edgeSet := by
      intro e he
      rcases Finset.mem_union.mp he with he | he
      · exact hB e he
      · exact hpath.subset_edgeSet e he
    exact ih (fun r hr => feasible r (by simp [hr])) _ hnext
      (greedyStep_isAcyclic G c hc B hB hforest q.1 q.2 _)

theorem greedy_isAcyclic (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    (SimpleGraph.fromEdgeSet (greedy G c requests feasible : Set (Sym2 V))).IsAcyclic :=
  greedy_isAcyclic_from G c hc requests feasible ∅ (by simp) (by simp)

end OnlineSteinerForest
