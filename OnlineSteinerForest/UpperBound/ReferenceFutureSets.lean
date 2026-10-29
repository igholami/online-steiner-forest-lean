import OnlineSteinerForest.UpperBound.BatchClasses

/-! The computed future pairs and marked endpoints in each strided batch class. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def futurePairs (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) : Finset (Fin requests.length) :=
  Finset.univ.filter fun i => ∃ d : Fin (requests.length.log2 + 1),
    d ∈ batchClass requests.length r ∧ b < d.val ∧ i ∈ costBatch G c requests feasible d

noncomputable def futureMarks (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) : Finset V :=
  (futurePairs G c requests feasible r b).biUnion fun i => {requests[i.val].1, requests[i.val].2}

theorem futurePairs_antitone (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) : Antitone (futurePairs G c requests feasible r) := by
  intro a b hab i hi
  obtain ⟨d, hd, hbd, hid⟩ := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hd, lt_of_le_of_lt hab hbd, hid⟩

theorem futureMarks_antitone (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) : Antitone (futureMarks G c requests feasible r) := by
  intro a b hab v hv
  obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨i, futurePairs_antitone G c requests feasible r hab hi, hvi⟩

theorem future_pair_endpoints_marked (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : ℕ) (i : Fin requests.length)
    (hi : i ∈ futurePairs G c requests feasible r b) :
    requests[i.val].1 ∈ futureMarks G c requests feasible r b ∧
      requests[i.val].2 ∈ futureMarks G c requests feasible r b := by
  constructor
  · exact Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩
  · exact Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩

end OnlineSteinerForest.UpperBound
