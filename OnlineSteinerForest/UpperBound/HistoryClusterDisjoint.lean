import OnlineSteinerForest.UpperBound.HistoryBlocks

/-! Distinct live clusters partition purchased edges without overlap. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clusterEdges_disjoint (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (C D : LabeledCluster ℕ) (hCD : Disjoint C.members D.members) :
    Disjoint (clusterEdges G c requests feasible C) (clusterEdges G c requests feasible D) := by
  apply Finset.disjoint_left.mpr
  intro e heC heD
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp heC
  obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp heD
  by_cases hij : i = j
  · subst j
    exact Finset.disjoint_left.mp hCD hi hj
  · exact Finset.disjoint_left.mp (purchasedBlocks_disjoint G c requests feasible hij) hei hej

theorem greedyHistory_active_edges_disjoint (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (C D : LabeledCluster ℕ)
    (hC : C ∈ (greedyHistory G c requests feasible i).active)
    (hD : D ∈ (greedyHistory G c requests feasible i).active) (hne : C ≠ D) :
    Disjoint (clusterEdges G c requests feasible C) (clusterEdges G c requests feasible D) :=
  clusterEdges_disjoint G c requests feasible C D
    ((greedyHistory_invariant G c requests feasible i).partition.disjoint C hC D hD hne)

end OnlineSteinerForest.UpperBound
