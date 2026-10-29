import OnlineSteinerForest.UpperBound.AuxiliaryLifetimePoint
import Mathlib.Data.Finset.Sort

/-! Sort the actual nonbirth requests of one label and use their actual far endpoints. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def labelBatch (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) : Finset (Fin requests.length) :=
  batch.filter (fun i => 0 < blockPayment G c requests feasible i.val ∧
    (touchedAt G c requests feasible i.val).Nonempty ∧ pairLabel G c requests feasible i.val = label)

noncomputable def orderedLabelRequest (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n) : Fin n ↪o Fin requests.length :=
  (labelBatch G c requests feasible batch label).orderEmbOfFin hcard

theorem orderedLabelRequest_mem (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n) (j : Fin n) :
    orderedLabelRequest G c requests feasible batch label hcard j ∈ labelBatch G c requests feasible batch label :=
  Finset.orderEmbOfFin_mem _ hcard j

noncomputable def labelFarSequence (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n) (j : Fin n) :
    lifetimeComponent G c requests feasible fallback label := by
  let i := orderedLabelRequest G c requests feasible batch label hcard j
  have hm := (Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard j)).2
  refine ⟨farVertex G c requests feasible i hm.2.1, ?_⟩
  have hmem := farVertex_in_lifetime G c hc requests feasible fallback i hm.1 hm.2.1
  exact Eq.mp (congrArg (fun l => farVertex G c requests feasible i hm.2.1 ∈
    lifetimeComponent G c requests feasible fallback l) hm.2.2) hmem

end OnlineSteinerForest.UpperBound
