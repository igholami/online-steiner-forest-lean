import OnlineSteinerForest.UpperBound.HistoryRequestLabels
import OnlineSteinerForest.UpperBound.HistoryComponents

/-! The selected old component for a nonbirth request in the actual greedy run. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def selectedRoot (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (ht : (touchedAt G c requests feasible i.val).Nonempty) : V :=
  requestSource requests requests[i.val].1 (MergeHistory.chosen (touchedAt G c requests feasible i.val) ht).label

theorem selectedRoot_after_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (ht : (touchedAt G c requests feasible i.val).Nonempty) :
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible (i.val + 1) : Set (Sym2 V))).Reachable
      requests[i.val].1 (selectedRoot G c requests feasible i ht) := by
  have hC := MergeHistory.chosen_mem (touchedAt G c requests feasible i.val) ht
  obtain ⟨hj, hlabel, hreach⟩ := (Finset.mem_filter.mp hC).2
  simpa only [selectedRoot, requestSource_eq requests requests[i.val].1 _ hlabel] using hreach

noncomputable def selectedComponent (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (ht : (touchedAt G c requests feasible i.val).Nonempty) : Finset V :=
  componentVertices (boughtBefore G c requests feasible i.val) (selectedRoot G c requests feasible i ht)

theorem selectedComponent_input_reach (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (ht : (touchedAt G c requests feasible i.val).Nonempty) :
    ∀ v ∈ selectedComponent G c requests feasible i ht, G.Reachable requests[i.val].1 v := by
  intro v hv
  have hroot := bought_reachable_input G _ (boughtBefore_input G c requests feasible (i.val + 1))
    (selectedRoot_after_connected G c requests feasible i ht)
  exact hroot.trans (bought_reachable_input G _ (boughtBefore_input G c requests feasible i.val)
    ((mem_componentVertices _ _ v).mp hv))

end OnlineSteinerForest.UpperBound
