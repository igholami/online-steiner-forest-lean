import OnlineSteinerForest.UpperBound.HistoryGreedy

/-! Disjoint purchased edge blocks realize the analysis members in the input graph. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def purchasedBlock (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    Finset (Sym2 V) :=
  boughtBefore G c requests feasible (i + 1) \ boughtBefore G c requests feasible i

theorem purchasedBlock_input (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) : ∀ e ∈ purchasedBlock G c requests feasible i, e ∈ G.edgeSet := by
  intro e he
  exact boughtBefore_input G c requests feasible (i + 1) e (Finset.mem_sdiff.mp he).1

theorem purchasedBlocks_disjoint (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    Pairwise (fun i j => Disjoint (purchasedBlock G c requests feasible i)
      (purchasedBlock G c requests feasible j)) := by
  intro i j hij
  wlog hlt : i < j generalizing i j
  · exact (this (i := j) (j := i) (Ne.symm hij) (by omega)).symm
  apply Finset.disjoint_left.mpr
  intro e hei hej
  exact (Finset.mem_sdiff.mp hej).2
    (boughtBefore_mono G c requests feasible (i + 1) j (by omega) (Finset.mem_sdiff.mp hei).1)

theorem purchasedBlock_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) :
    edgeCost c (purchasedBlock G c requests feasible i.val) = payment G c requests feasible i := by
  rw [payment_eq_cost_increment]
  exact eq_sub_of_add_eq (Finset.sum_sdiff (f := c)
    (boughtBefore_mono G c requests feasible i.val (i.val + 1) (by omega)))

/-- The actual purchased edges assigned to a component snapshot. -/
noncomputable def clusterEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (C : LabeledCluster ℕ) : Finset (Sym2 V) :=
  C.members.biUnion (purchasedBlock G c requests feasible)

theorem clusterEdges_cost (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (C : LabeledCluster ℕ) (hC : ∀ i ∈ C.members, i < requests.length) :
    edgeCost c (clusterEdges G c requests feasible C) =
      clusterWeight (blockPayment G c requests feasible) C := by
  rw [edgeCost, clusterEdges, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    simpa [blockPayment, hC i hi, edgeCost] using purchasedBlock_cost G c requests feasible ⟨i, hC i hi⟩
  · intro i hi j hj hij
    exact purchasedBlocks_disjoint G c requests feasible hij

end OnlineSteinerForest.UpperBound
