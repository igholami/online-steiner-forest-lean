import OnlineSteinerForest.UpperBound.OmissionsLabelBounds

/-! Total payment of the computed omissions for one label, including empty batches. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def firstOmittedLabelPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) : ℝ :=
  if h : (labelBatch G c requests feasible batch label).Nonempty then
    let hcard : (labelBatch G c requests feasible batch label).card =
        (labelBatch G c requests feasible batch label).card - 1 + 1 := by have := Finset.card_pos.mpr h; omega
    ∑ j ∈ firstLabelPositions G c requests feasible batch label hcard,
      blockPayment G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard j).val
  else 0

noncomputable def longOmittedLabelPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) (scale : ℝ) : ℝ :=
  if h : (labelBatch G c requests feasible batch label).Nonempty then
    let hcard : (labelBatch G c requests feasible batch label).card =
        (labelBatch G c requests feasible batch label).card - 1 + 1 := by have := Finset.card_pos.mpr h; omega
    ∑ j ∈ longLabelPositions G c hc requests feasible fallback batch label hcard scale,
      blockPayment G c requests feasible (orderedLabelRequest G c requests feasible batch label hcard (newIndex j)).val
  else 0

theorem first_omitted_label_scaled (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) (label : ℕ) :
    (64 * (cycleFactor requests.length : ℝ) ^ 2) * firstOmittedLabelPayment G c requests feasible batch label ≤
      clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) := by
  unfold firstOmittedLabelPayment
  split_ifs with hn
  · exact first_label_payment_bound G c hc requests feasible batch label _
  · simp only [mul_zero]
    exact Finset.sum_nonneg (fun a ha => blockPayment_nonneg G c hc requests feasible a)

theorem long_omitted_label_scaled (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) (scale : ℝ)
    (hbatch : ∀ i ∈ batch, blockPayment G c requests feasible i.val ≤ 2 * scale) :
    (128 * (cycleFactor requests.length : ℝ) ^ 3) * longOmittedLabelPayment G c hc requests feasible fallback batch label scale ≤
      2 * cycleFactor requests.length * clusterWeight (blockPayment G c requests feasible)
        (finalLifetime G c requests feasible label) := by
  unfold longOmittedLabelPayment
  split_ifs with hn
  · exact long_label_payment_bound G c hc requests feasible fallback batch label _ scale hbatch
  · simp only [mul_zero]
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun a ha => blockPayment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible a)

end OnlineSteinerForest.UpperBound
