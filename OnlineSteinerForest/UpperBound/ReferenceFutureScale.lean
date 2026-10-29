import OnlineSteinerForest.UpperBound.ReferenceFutureSets
import OnlineSteinerForest.UpperBound.BatchSeparation

/-! Every future pair has payment separated from the current batch by the full stride. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem future_pair_payment_ge (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (r : Fin (batchClassCount requests.length)) (b : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r) (i : Fin requests.length)
    (hi : i ∈ futurePairs G c requests feasible r b.val) :
    (2 : ℝ) ^ batchClassCount requests.length * batchScale G c requests feasible b.val ≤
      payment G c requests feasible i := by
  obtain ⟨d, hd, hbd, hid⟩ := (Finset.mem_filter.mp hi).2
  exact (batchClass_scale_gap G c requests feasible hk ho r b d hb hd hbd).trans
    (costBatch_band G c requests feasible hk ho d i hid).1

end OnlineSteinerForest.UpperBound
