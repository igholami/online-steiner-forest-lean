import OnlineSteinerForest.UpperBound.AuxiliaryBirthPath
import OnlineSteinerForest.UpperBound.AuxiliaryRealization

/-! The direct branch returns an actual simple input path with the manuscript cost bound. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem lifetimeEdges_input (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (label : ℕ) :
    ∀ e ∈ clusterEdges G c requests feasible (finalLifetime G c requests feasible label), e ∈ G.edgeSet := by
  intro e he
  obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
  exact purchasedBlock_input G c requests feasible j e he

theorem request_reachable_in_lifetime (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val) :
    (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible
      (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)) : Set (Sym2 V))).Reachable
      requests[i.val].1 requests[i.val].2 :=
  (finalLifetime_requests_connected G c hc requests feasible (i.val + 1) (by omega)
    (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))
    i i (MergeHistory.new_mem_merged _ _) (MergeHistory.new_mem_merged _ _)).2

noncomputable def directAuxEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val) : Finset (Sym2 V) :=
  if isBirth G c requests feasible i.val then shortestPathEdges G c (boughtBefore G c requests feasible i.val)
    requests[i.val].1 requests[i.val].2 (feasible _ (List.getElem_mem i.isLt))
  else realizingEdges G (clusterEdges G c requests feasible
    (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)))
    (lifetimeEdges_input G c requests feasible _) requests[i.val].1 requests[i.val].2
    (request_reachable_in_lifetime G c hc requests feasible i hp)

theorem directAuxEdges_spec (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val) :
    IsPathEdges G requests[i.val].1 requests[i.val].2 (directAuxEdges G c hc requests feasible i hp) := by
  unfold directAuxEdges
  split_ifs
  · exact (shortestPathEdges_spec G c _ _ _ _).1
  · exact (realizingEdges_spec G _ _ _ _ _).1

theorem lifetimeEdges_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (hp : 0 < blockPayment G c requests feasible i.val) :
    edgeCost c (clusterEdges G c requests feasible
      (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val))) =
    clusterWeight (blockPayment G c requests feasible)
      (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)) := by
  have hC := (finalLifetime_contains_snapshot G c requests feasible (i.val + 1) (by omega)
    (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))).1
  exact clusterEdges_cost G c requests feasible _
    (greedyHistory_snapshot_members G c requests feasible requests.length _ hC)

theorem directAuxEdges_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val) (L : ℝ) (hL : 1 ≤ L)
    (hbranch : isBirth G c requests feasible i.val ∨
      clusterWeight (blockPayment G c requests feasible)
        (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)) ≤
          64 * L ^ 2 * payment G c requests feasible i) :
    edgeCost c (directAuxEdges G c hc requests feasible i hp) ≤ 64 * L ^ 2 * payment G c requests feasible i := by
  unfold directAuxEdges
  split_ifs with hb
  · rw [birth_path_original_cost G c hc requests feasible i hb]
    have hn := payment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible i
    have hmul : 1 ≤ 64 * L ^ 2 := by nlinarith [sq_nonneg (L - 1)]
    nlinarith [mul_le_mul_of_nonneg_right hmul hn]
  · have hcost := realizingEdges_cost_le G c (fun e he => le_of_lt (hc e he)) _
      (lifetimeEdges_input G c requests feasible _) _ _ (request_reachable_in_lifetime G c hc requests feasible i hp)
    rw [lifetimeEdges_cost G c requests feasible i hp] at hcost
    exact hcost.trans (hbranch.resolve_left hb)

end OnlineSteinerForest.UpperBound
