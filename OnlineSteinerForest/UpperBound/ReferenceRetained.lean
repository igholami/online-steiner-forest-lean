import OnlineSteinerForest.UpperBound.RetainedReplacement
import OnlineSteinerForest.UpperBound.ReferenceClassState
import OnlineSteinerForest.UpperBound.ReferenceClassSavings
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceExtraction

/-! Instantiate the geometric replacement bound with actual retained outputs and class states. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem class_retained_count_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (r : Fin (batchClassCount requests.length)) (b : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r) :
    ((retainedReferenceRequests G c hc requests feasible fallback
      (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val b).card : ℝ) *
      batchScale G c requests feasible b.val ≤
    32 * cycleFactor requests.length * classSaving G c (fun e he => (hc e he).le) requests feasible r b.val +
      2 ^ 24 * (cycleFactor requests.length : ℝ) ^ 4 *
        (futureMarks G c requests feasible r b.val).card * batchScale G c requests feasible b.val +
      2 ^ 28 * cycleFactor (cycleFactor requests.length) *
        edgeCost c (classReference G c (fun e he => (hc e he).le) requests feasible r b.val).val := by
  let hc₀ := fun e he => (hc e he).le
  let F := (classReference G c hc₀ requests feasible r b.val).val
  let J := retainedReferenceRequests G c hc requests feasible fallback F b
  let time : ↥J ↪ Fin requests.length := ⟨Subtype.val, Subtype.val_injective⟩
  let out : ↥J → AuxiliaryOutput V := fun i =>
    retainedReferenceOutput G c hc requests feasible fallback F b i.val i.property
  have hhelpful : ∀ i : ↥J, HelpfulAt G c requests feasible (time i)
      (batchScale G c requests feasible b.val) (out i) := fun i =>
    retainedReferenceOutput_helpful G c hc requests feasible fallback hk ho F b i.val i.property
  have hlarge : ∀ i : ↥J,
      65536 * (cycleFactor requests.length : ℝ) ^ 3 * batchScale G c requests feasible b.val ≤
        referenceTreeCost F c (out i).left ∧
      65536 * (cycleFactor requests.length : ℝ) ^ 3 * batchScale G c requests feasible b.val ≤
        referenceTreeCost F c (out i).right := fun i =>
    retainedReferenceOutput_large G c hc requests feasible fallback F b
      (classReference_connects_batch G c hc₀ requests feasible r b hb) i.val i.property
  have h := retained_replacement_count G c hc₀ requests feasible F
    (classReference G c hc₀ requests feasible r b.val).property
    (classReference_isAcyclic G c hc₀ requests feasible r b.val) time out
    (batchScale G c requests feasible b.val) (batchScale_pos G c requests feasible hk ho b.val)
    hhelpful hlarge (futureMarks G c requests feasible r b.val)
  simpa only [Fintype.card_coe, classSaving, classReference_succ] using h

end OnlineSteinerForest.UpperBound
