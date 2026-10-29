import OnlineSteinerForest.UpperBound.OmissionsFamily
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceSplit

/-! The exclusion losses for the computed large-pair sets of any reference-forest run. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem first_reference_family_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (refs : Fin (requests.length.log2 + 1) → Finset (Sym2 V)) :
    ∑ b, firstOmittedBatchPayment G c requests feasible
      (largeReferencePairs c requests (refs b) (costBatch G c requests feasible b) (batchScale G c requests feasible b.val)) ≤
      greedyCost G c requests feasible / 64 :=
  first_omissions_family_bound G c hc requests feasible _

theorem long_reference_family_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (refs : Fin (requests.length.log2 + 1) → Finset (Sym2 V)) :
    ∑ b, longOmittedBatchPayment G c hc requests feasible fallback
      (largeReferencePairs c requests (refs b) (costBatch G c requests feasible b) (batchScale G c requests feasible b.val))
      (batchScale G c requests feasible b.val) ≤ greedyCost G c requests feasible / 64 :=
  long_omissions_family_bound G c hc requests feasible fallback hk ho _
    (fun b => largeReferencePairs_subset c requests (refs b) _ _)

end OnlineSteinerForest.UpperBound
