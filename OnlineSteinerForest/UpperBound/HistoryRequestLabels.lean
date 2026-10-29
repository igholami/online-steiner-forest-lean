import OnlineSteinerForest.UpperBound.HistoryFinalLifetime

/-! The manuscript's chronological birth/nonbirth labels, with union-by-size survivors. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def touchedAt (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    Finset (LabeledCluster ℕ) :=
  (greedyHistory G c requests feasible i).active.filter (touchesBlock G c requests feasible i)

noncomputable def requestCluster (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) : LabeledCluster ℕ :=
  MergeHistory.merged i (touchedAt G c requests feasible i)

noncomputable def pairLabel (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) : ℕ :=
  (requestCluster G c requests feasible i).label

noncomputable def isBirth (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) : Prop :=
  touchedAt G c requests feasible i = ∅

theorem requestCluster_active (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (hp : 0 < blockPayment G c requests feasible i) :
    requestCluster G c requests feasible i ∈ (greedyHistory G c requests feasible (i + 1)).active := by
  change _ ∈ (scanHistory _ _ (i + 1)).active
  rw [scanHistory, if_pos hp]
  exact Finset.mem_insert_self _ _

theorem selectedOld_active (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (ht : (touchedAt G c requests feasible i).Nonempty) :
    MergeHistory.chosen (touchedAt G c requests feasible i) ht ∈
      (greedyHistory G c requests feasible i).active :=
  (Finset.mem_filter.mp (MergeHistory.chosen_mem _ ht)).1

theorem selectedOld_label (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (ht : (touchedAt G c requests feasible i).Nonempty) :
    (MergeHistory.chosen (touchedAt G c requests feasible i) ht).label =
      pairLabel G c requests feasible i :=
  (MergeHistory.winner_label_of_nonempty i _ ht).symm

theorem request_mem_finalLifetime (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) (hp : 0 < blockPayment G c requests feasible i.val) :
    i.val ∈ (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)).members := by
  exact (finalLifetime_contains_snapshot G c requests feasible (i.val + 1) (by omega)
    (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hp))).2.1
      (MergeHistory.new_mem_merged _ _)

end OnlineSteinerForest.UpperBound
