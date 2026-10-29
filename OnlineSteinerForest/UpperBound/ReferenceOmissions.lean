import OnlineSteinerForest.UpperBound.ReferenceBatchOwner
import OnlineSteinerForest.UpperBound.OmissionsReferenceFamily

/-! The omission loss for the actual canonical reference family is at most ALG/32. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def referenceOmittedPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (b : Fin (requests.length.log2 + 1)) : ℝ :=
  let F := (batchReference G c (fun e he => (hc e he).le) requests feasible b).val
  let large := largeReferencePairs c requests F (costBatch G c requests feasible b)
    (batchScale G c requests feasible b.val)
  firstOmittedBatchPayment G c requests feasible large +
    longOmittedBatchPayment G c hc requests feasible fallback large (batchScale G c requests feasible b.val)

theorem referenceOmitted_sum_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) :
    (∑ b, referenceOmittedPayment G c hc requests feasible fallback b) ≤
      greedyCost G c requests feasible / 32 := by
  have hf := first_reference_family_bound G c (fun e he => (hc e he).le) requests feasible
    (fun b => (batchReference G c (fun e he => (hc e he).le) requests feasible b).val)
  have hl := long_reference_family_bound G c hc requests feasible fallback hk ho
    (fun b => (batchReference G c (fun e he => (hc e he).le) requests feasible b).val)
  simp only [referenceOmittedPayment, Finset.sum_add_distrib]
  linarith

theorem referenceOmitted_class_sum_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) :
    (∑ r : Fin (batchClassCount requests.length), ∑ b ∈ batchClass requests.length r,
      referenceOmittedPayment G c hc requests feasible fallback b) ≤ greedyCost G c requests feasible / 32 := by
  rw [← Finset.sum_biUnion (fun r hr s hs hrs => batchClass_disjoint _ r s hrs), batchClass_union]
  exact referenceOmitted_sum_le G c hc requests feasible fallback hk ho

end OnlineSteinerForest.UpperBound
