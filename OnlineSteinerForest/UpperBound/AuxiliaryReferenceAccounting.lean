import OnlineSteinerForest.UpperBound.AuxiliaryBatchAccounting
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceExtraction

/-! Concrete reference-forest accounting at every computed dyadic cost bucket. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem costBatch_reference_accounting (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (F : Finset (Sym2 V)) (b : Fin (requests.length.log2 + 1)) :
    ∑ i ∈ costBatch G c requests feasible b, payment G c requests feasible i ≤
      (∑ i ∈ smallReferencePairs c requests F (costBatch G c requests feasible b)
        (batchScale G c requests feasible b.val), payment G c requests feasible i) +
      2 * batchScale G c requests feasible b.val * (retainedReferenceRequests G c hc requests feasible fallback F b).card +
      firstOmittedBatchPayment G c requests feasible
        (largeReferencePairs c requests F (costBatch G c requests feasible b) (batchScale G c requests feasible b.val)) +
      longOmittedBatchPayment G c hc requests feasible fallback
        (largeReferencePairs c requests F (costBatch G c requests feasible b) (batchScale G c requests feasible b.val))
        (batchScale G c requests feasible b.val) := by
  apply batch_reference_accounting G c hc requests feasible fallback F _ _
    (batchScale_pos G c requests feasible hk ho b.val)
  intro i hi
  have hband := costBatch_band G c requests feasible hk ho b i hi
  exact ⟨hband.1, le_of_lt hband.2⟩

end OnlineSteinerForest.UpperBound
