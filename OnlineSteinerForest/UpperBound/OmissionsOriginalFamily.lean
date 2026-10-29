import OnlineSteinerForest.UpperBound.OmissionsOriginalPayments
import OnlineSteinerForest.UpperBound.OmissionsFamily

/-! ALG/64 omission bounds expressed as sums over original request indices. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem first_original_family_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (selection : Fin (requests.length.log2 + 1) → Finset (Fin requests.length)) :
    ∑ b, ∑ i ∈ firstOmittedRequests G c requests feasible (selection b), payment G c requests feasible i ≤
      greedyCost G c requests feasible / 64 :=
  (Finset.sum_le_sum (fun b _ => firstOmittedRequests_payment_le G c hc requests feasible (selection b))).trans
    (first_omissions_family_bound G c hc requests feasible selection)

theorem long_original_family_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (selection : Fin (requests.length.log2 + 1) → Finset (Fin requests.length))
    (hselection : ∀ b, selection b ⊆ costBatch G c requests feasible b) :
    ∑ b, ∑ i ∈ longOmittedRequests G c hc requests feasible fallback (selection b)
      (batchScale G c requests feasible b.val), payment G c requests feasible i ≤
      greedyCost G c requests feasible / 64 :=
  (Finset.sum_le_sum (fun b _ => longOmittedRequests_payment_le G c hc requests feasible fallback
    (selection b) (batchScale G c requests feasible b.val))).trans
    (long_omissions_family_bound G c hc requests feasible fallback hk ho selection hselection)

end OnlineSteinerForest.UpperBound
