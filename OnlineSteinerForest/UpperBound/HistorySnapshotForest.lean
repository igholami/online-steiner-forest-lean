import OnlineSteinerForest.UpperBound.HistoryBlocks

/-! Every lifetime snapshot consists of actual greedy edges and is a standard forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clusterEdges_subset_bought (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (C : LabeledCluster ℕ) (i : ℕ) (hC : ∀ j ∈ C.members, j < i) :
    clusterEdges G c requests feasible C ⊆ boughtBefore G c requests feasible i := by
  intro e he
  obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
  exact boughtBefore_mono G c requests feasible (j + 1) i (by have := hC j hj; omega)
    (Finset.mem_sdiff.mp he).1

theorem clusterEdges_isAcyclic (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (C : LabeledCluster ℕ) (i : ℕ) (hC : ∀ j ∈ C.members, j < i) :
    (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).IsAcyclic :=
  (boughtBefore_isAcyclic G c hc requests feasible i).anti
    (SimpleGraph.fromEdgeSet_mono (clusterEdges_subset_bought G c requests feasible C i hC))

/-- Both live component snapshots and retired lifetimes use only earlier blocks. -/
theorem greedyHistory_snapshot_members (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (C : LabeledCluster ℕ)
    (hC : C ∈ (greedyHistory G c requests feasible i).active ∨
      C ∈ (greedyHistory G c requests feasible i).retired) :
    ∀ j ∈ C.members, j < i := by
  have h := greedyHistory_invariant G c requests feasible i
  have hsub : C.members ⊆ scannedBlocks (fun j => 0 < blockPayment G c requests feasible j) i := by
    rcases hC with hC | hC
    · exact h.partition.member_subset C hC
    · exact h.archive C hC
  intro j hj
  exact Finset.mem_range.mp (Finset.mem_filter.mp (hsub hj)).1

theorem greedyHistory_snapshot_forest (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (C : LabeledCluster ℕ)
    (hC : C ∈ (greedyHistory G c requests feasible i).active ∨
      C ∈ (greedyHistory G c requests feasible i).retired) :
    (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).IsAcyclic :=
  clusterEdges_isAcyclic G c hc requests feasible C i
    (greedyHistory_snapshot_members G c requests feasible i C hC)

end OnlineSteinerForest.UpperBound
