import OnlineSteinerForest.UpperBound.GirthResidualDistance
import OnlineSteinerForest.UpperBound.HistoryPrefixConnected

/-! The actual greedy prefix metrics satisfy the chronological threshold hypotheses. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def requestMetric (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) :
    V → V → ENNReal := residualEDistance G c (boughtBefore G c requests feasible i)

theorem requestMetric_refl (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (v : V) :
    requestMetric G c requests feasible i v v = 0 := residualEDistance_refl G c hc _ v

theorem requestMetric_triangle (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (u v z : V) :
    requestMetric G c requests feasible i u z ≤ requestMetric G c requests feasible i u v +
      requestMetric G c requests feasible i v z := residualEDistance_triangle G c hc _ u v z

theorem requestMetric_symm (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (u v : V) :
    requestMetric G c requests feasible i u v = requestMetric G c requests feasible i v u :=
  residualEDistance_symm G c _ u v

theorem requestMetric_payment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) :
    requestMetric G c requests feasible i.val requests[i.val].1 requests[i.val].2 =
      ENNReal.ofReal (payment G c requests feasible i) :=
  residualEDistance_of_reachable G c _ _ _ (feasible _ (List.getElem_mem i.isLt))

theorem requestMetric_prior_zero (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (j : Fin requests.length) (i : ℕ) (hji : j.val < i) :
    requestMetric G c requests feasible i requests[j.val].1 requests[j.val].2 = 0 := by
  rw [requestMetric, residualEDistance_of_reachable G c _ _ _ (feasible _ (List.getElem_mem j.isLt)),
    residualDistance_eq_zero_of_bought G c hc _ (boughtBefore_input G c requests feasible i)
      _ _ _ (request_reachable_after G c requests feasible j i hji)]
  simp

theorem residualEDistance_adj_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (B : Finset (Sym2 V)) {u v : V} (huv : G.Adj u v) :
    residualEDistance G c B u v ≤ ENNReal.ofReal (c s(u, v)) := by
  have hinput : ∀ e ∈ ({s(u, v)} : Finset (Sym2 V)), e ∈ G.edgeSet := by
    intro e he
    rw [Finset.mem_singleton.mp he]
    exact G.mem_edgeSet.mpr huv
  have hconn : (SimpleGraph.fromEdgeSet (({s(u, v)} : Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
    exact SimpleGraph.Adj.reachable ⟨by simp, huv.ne⟩
  have hh := shortestPathEdges_cost_le c hc B u v huv.reachable {s(u, v)} hinput hconn
  rw [residualEDistance_of_reachable G c B u v huv.reachable]
  apply ENNReal.ofReal_le_ofReal
  simpa only [residualDistance, edgeCost, Finset.sum_singleton] using hh

theorem request_positive_endpoints_ne (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hi : 0 < payment G c requests feasible i) : requests[i.val].1 ≠ requests[i.val].2 := by
  intro heq
  have hm := requestMetric_payment G c requests feasible i
  rw [heq, requestMetric_refl G c hc requests feasible i.val] at hm
  exact (ENNReal.ofReal_pos.mpr hi).ne' hm.symm

end OnlineSteinerForest.UpperBound
