import OnlineSteinerForest.Graph.GreedyForest
import OnlineSteinerForest.Graph.ResidualMetric
import OnlineSteinerForest.Greedy.Payments

/-! Time-indexed purchased graphs are prefixes of the implemented greedy execution. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Composition law for the actual online algorithm. -/
theorem greedy_append (G : SimpleGraph V) (c : Sym2 V → ℝ) (xs ys : List (V × V))
    (h : ∀ q ∈ xs ++ ys, G.Reachable q.1 q.2) (B : Finset (Sym2 V)) :
    greedy G c (xs ++ ys) h B =
      greedy G c ys (fun q hq => h q (List.mem_append_right _ hq))
        (greedy G c xs (fun q hq => h q (List.mem_append_left _ hq)) B) := by
  induction xs generalizing B with
  | nil => rfl
  | cons q xs ih =>
    simp only [List.cons_append, greedy]
    exact ih _ _

/-- List equality changes only the proof of feasibility supplied to the implementation. -/
theorem greedy_congr_requests (G : SimpleGraph V) (c : Sym2 V → ℝ) (xs ys : List (V × V))
    (hx : ∀ q ∈ xs, G.Reachable q.1 q.2) (hy : ∀ q ∈ ys, G.Reachable q.1 q.2)
    (hxy : xs = ys) (B : Finset (Sym2 V)) : greedy G c xs hx B = greedy G c ys hy B := by
  subst ys
  rfl

/-- Edges purchased strictly before request index `i` (indices start at zero). -/
noncomputable def boughtBefore (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    Finset (Sym2 V) :=
  greedy G c (requests.take i) (fun q hq => feasible q (List.mem_of_mem_take hq))

@[simp] theorem boughtBefore_zero (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    boughtBefore G c requests feasible 0 = ∅ := rfl

@[simp] theorem boughtBefore_length (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    boughtBefore G c requests feasible requests.length = greedy G c requests feasible := by
  simp only [boughtBefore, List.take_length]

theorem boughtBefore_input (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    ∀ e ∈ boughtBefore G c requests feasible i, e ∈ G.edgeSet :=
  (greedy_feasible G c (requests.take i) _).1

theorem boughtBefore_isAcyclic (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).IsAcyclic :=
  greedy_isAcyclic G c hc _ _

/-- The exact residual payment of request `i`. -/
noncomputable def payment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) : ℝ :=
  residualDistance G c (boughtBefore G c requests feasible i.val) requests[i.val].1 requests[i.val].2
    (feasible requests[i.val] (List.getElem_mem i.isLt))

theorem payment_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length) :
    0 ≤ payment G c requests feasible i := residualDistance_nonneg G c hc _ _ _ _

theorem boughtBefore_mono (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i j : ℕ) (hij : i ≤ j) :
    boughtBefore G c requests feasible i ⊆ boughtBefore G c requests feasible j := by
  have heq : requests.take j = requests.take i ++ (requests.take j).drop i := by
    simpa only [List.take_take, Nat.min_eq_left hij] using
      (List.take_append_drop i (requests.take j)).symm
  have hconn : ∀ q ∈ requests.take i ++ (requests.take j).drop i, G.Reachable q.1 q.2 := by
    intro q hq
    rw [← heq] at hq
    exact feasible q (List.mem_of_mem_take hq)
  have hg := greedy_append G c (requests.take i) ((requests.take j).drop i) hconn ∅
  have hsub := greedy_extends G c ((requests.take j).drop i)
    (fun q hq => hconn q (List.mem_append_right _ hq))
    (greedy G c (requests.take i) (fun q hq => hconn q (List.mem_append_left _ hq)) ∅)
  unfold boughtBefore
  rw [greedy_congr_requests G c _ _ _ hconn heq ∅, hg]
  exact hsub

end OnlineSteinerForest.UpperBound
