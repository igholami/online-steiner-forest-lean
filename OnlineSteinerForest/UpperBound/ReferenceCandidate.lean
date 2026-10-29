import OnlineSteinerForest.UpperBound.ReferenceUpdate

/-! Every concrete replacement candidate bounds the actual canonical reference update. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem referenceUpdate_cost_le_candidate (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) (A : Finset (Sym2 V))
    (hA : ∀ e ∈ A, e ∈ G.edgeSet)
    (hpreserve : ∀ u ∈ marks, ∀ v ∈ marks,
      (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable u v →
      (SimpleGraph.fromEdgeSet (A : Set (Sym2 V))).Reachable u v) :
    edgeCost c (referenceUpdate G c hc F hF marks) ≤ edgeCost c A := by
  rw [(referenceUpdate_spec G c hc F hF marks).2.2]
  apply optimum_le
  refine ⟨hA, ?_⟩
  intro q hq
  obtain ⟨hu, hv, hr⟩ := (mem_markedRequests F marks q.1 q.2).mp hq
  exact hpreserve q.1 hu q.2 hv hr

theorem referenceUpdate_cost_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) :
    edgeCost c (referenceUpdate G c hc F hF marks) ≤ edgeCost c F :=
  referenceUpdate_cost_le_candidate G c hc F hF marks F hF (fun _ _ _ _ h => h)

theorem referenceUpdate_cost_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (F : Finset (Sym2 V))
    (hF : ∀ e ∈ F, e ∈ G.edgeSet) (marks : Finset V) :
    0 ≤ edgeCost c (referenceUpdate G c hc F hF marks) := by
  apply Finset.sum_nonneg
  intro e he
  exact hc e ((referenceUpdate_spec G c hc F hF marks).1.1 e he)

end OnlineSteinerForest.UpperBound
