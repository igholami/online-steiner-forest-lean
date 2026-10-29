import OnlineSteinerForest.UpperBound.ReferenceFutureSets

/-! Each future pair contributes at most two original marked endpoints. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem futureMarks_card_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    (futureMarks G c requests feasible r b).card ≤
      2 * (futurePairs G c requests feasible r b).card := by
  calc
    _ ≤ ∑ i ∈ futurePairs G c requests feasible r b,
        ({requests[i.val].1, requests[i.val].2} : Finset V).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ futurePairs G c requests feasible r b, 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ = _ := by simp [Nat.mul_comm]

theorem futurePairs_card_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) :
    (futurePairs G c requests feasible r b).card ≤ requests.length := by
  simpa only [Fintype.card_fin] using
    (Finset.card_le_univ (s := futurePairs G c requests feasible r b))

end OnlineSteinerForest.UpperBound
