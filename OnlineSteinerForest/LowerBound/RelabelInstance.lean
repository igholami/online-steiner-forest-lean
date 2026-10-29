import OnlineSteinerForest.LowerBound.RelabelRun
import OnlineSteinerForest.LowerBound.GreedyCost
import OnlineSteinerForest.LowerBound.OfflineBound

/-! The manuscript instance expressed on any equivalent vertex type, including `Fin n`. -/
namespace OnlineSteinerForest.LowerBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W : Type} [Fintype W] [DecidableEq W]

noncomputable def relabelInstanceGraph (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) : SimpleGraph W := (instanceGraph h σ).map e

noncomputable def relabelInstanceRequests (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) : List (W × W) := relabelRequests e (instanceRequests h σ)

omit [Fintype W] in
theorem relabelInstance_feasible (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) : ∀ q ∈ relabelInstanceRequests h σ e,
    (relabelInstanceGraph h σ e).Reachable q.1 q.2 :=
  requests_relabel_feasible (SimpleGraph.Iso.map e _) _ (instance_feasible h σ)

theorem relabelInstance_greedy_edges (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) :
    greedy (relabelInstanceGraph h σ e) (relabelCost e (constructionCost (rankPrice h)))
      (relabelInstanceRequests h σ e) (relabelInstance_feasible h σ e) =
      relabelEdges e ((retainedRanks h σ).biUnion (matchingEdges σ)) := by
  let R := retainedRanks h σ
  have hrequests : relabelRankRequests h e σ (R.sort (· ≤ ·)) = relabelInstanceRequests h σ e := by
    simp [relabelRankRequests, relabelInstanceRequests, relabelRequests, instanceRequests,
      requestedPairs, List.map_map, R, Function.comp_def]
  have hg := greedy_relabel_rank_list h e σ R (R.sort (· ≤ ·))
    (fun i hi => (Finset.mem_sort (· ≤ ·)).mp hi)
    (fun i hi => (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hi)).2.2)
    R.sortedLT_sort.pairwise ∅ (by simp)
    (by rw [hrequests]; exact relabelInstance_feasible h σ e)
  simpa only [hrequests, Finset.biUnion_empty, relabelEdges_empty, Finset.empty_union,
    Finset.sort_toFinset, R, relabelInstanceGraph, instanceGraph] using hg

theorem relabelInstance_greedy_cost (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) :
    greedyCost (relabelInstanceGraph h σ e) (relabelCost e (constructionCost (rankPrice h)))
      (relabelInstanceRequests h σ e) (relabelInstance_feasible h σ e) =
      ∑ i ∈ retainedRanks h σ, rankPrice h i := by
  unfold greedyCost
  rw [relabelInstance_greedy_edges, edgeCost_relabel, matching_union_cost]

theorem relabelInstance_optimum_le (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) :
    optimum (relabelInstanceGraph h σ e) (relabelCost e (constructionCost (rankPrice h)))
      (relabelInstanceRequests h σ e) (relabelInstance_feasible h σ e) ≤ (vertexCount h : ℝ) - 1 :=
  (optimum_relabel_le (SimpleGraph.Iso.map e _) _ _ (instance_feasible h σ) _).trans
    (instance_optimum_le_path h σ)

theorem relabelInstance_optimum_eq (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) :
    optimum (relabelInstanceGraph h σ e) (relabelCost e (constructionCost (rankPrice h)))
      (relabelInstanceRequests h σ e) (relabelInstance_feasible h σ e) =
      optimum (instanceGraph h σ) (constructionCost (rankPrice h)) (instanceRequests h σ)
        (instance_feasible h σ) :=
  optimum_relabel_eq (SimpleGraph.Iso.map e _) _ _ (instance_feasible h σ) _

omit [Fintype W] in
theorem relabelInstance_positive (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) : ∀ x ∈ (relabelInstanceGraph h σ e).edgeSet,
    0 < relabelCost e (constructionCost (rankPrice h)) x := by
  intro x hx
  obtain ⟨y, rfl⟩ := (edgeEquiv e).surjective x
  rw [relabelCost_apply]
  exact instance_positive h σ y ((SimpleGraph.Iso.map e _).map_mem_edgeSet_iff.mp hx)

omit [Fintype W] [DecidableEq W] in
@[simp] theorem relabelInstance_requests_length (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (e : Vertex (matchingSize h) ≃ W) :
    (relabelInstanceRequests h σ e).length = (instanceRequests h σ).length := by
  simp [relabelInstanceRequests, relabelRequests]

/-- Canonical finite labels for every vertex of the concrete construction. -/
noncomputable def vertexLabels (m : ℕ) : Vertex m ≃ Fin (Fintype.card (Vertex m)) :=
  Fintype.equivFin (Vertex m)

@[simp] theorem construction_vertex_card (m : ℕ) : Fintype.card (Vertex m) = 3 * m := by
  simp only [Vertex, Fintype.card_sum, Fintype.card_fin]
  omega

end OnlineSteinerForest.LowerBound
