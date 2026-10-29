import OnlineSteinerForest.UpperBound.AuxiliaryLabelSequence

/-! Invert the chronological ordering to locate an actual request in its label batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def labelPosition (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n)
    (i : Fin requests.length) (hi : i ∈ labelBatch G c requests feasible batch label) : Fin n :=
  ((labelBatch G c requests feasible batch label).orderIsoOfFin hcard).symm ⟨i, hi⟩

theorem orderedLabelRequest_labelPosition (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n)
    (i : Fin requests.length) (hi : i ∈ labelBatch G c requests feasible batch label) :
    orderedLabelRequest G c requests feasible batch label hcard
      (labelPosition G c requests feasible batch label hcard i hi) = i := by
  change (((labelBatch G c requests feasible batch label).orderIsoOfFin hcard)
    (((labelBatch G c requests feasible batch label).orderIsoOfFin hcard).symm ⟨i, hi⟩)).val = i
  rw [OrderIso.apply_symm_apply]

end OnlineSteinerForest.UpperBound
