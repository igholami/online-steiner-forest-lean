import OnlineSteinerForest.UpperBound.HistoryLabelUniqueness
import OnlineSteinerForest.UpperBound.HistoryLifetime
import OnlineSteinerForest.UpperBound.HistoryRequestsConnected

/-! Earlier requests bearing a live label are already inside its present old component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem earlier_same_label_members (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i j : ℕ) (hij : i ≤ j) (C D : LabeledCluster ℕ)
    (hC : IsSnapshot (greedyHistory G c requests feasible i) C)
    (hD : IsSnapshot (greedyHistory G c requests feasible j) D) (hl : C.label = D.label) :
    C.members ⊆ D.members := by
  obtain ⟨E, hE, hEl, hs⟩ := scanHistory_persists
    (fun k => 0 < blockPayment G c requests feasible k) (touchesBlock G c requests feasible) i j hij C hC
  have heq := greedyHistory_snapshot_label_unique G c requests feasible j E D hE hD (hEl.trans hl)
  simpa only [heq] using hs

end OnlineSteinerForest.UpperBound
