import OnlineSteinerForest.UpperBound.OmissionsBatchBounds
import OnlineSteinerForest.UpperBound.BatchAlgorithm

/-! The manuscript's ALG/64 first and long losses across the computed dyadic bucket family. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem finite_bucket_budget (k : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (f : Fin (k.log2 + 1) → ℝ) (hf : ∀ b, f b ≤ A / (64 * cycleFactor k)) :
    ∑ b, f b ≤ A / 64 := by
  have hL : 0 < (cycleFactor k : ℝ) := Nat.cast_pos.mpr (cycleFactor_pos k)
  calc
    _ ≤ ∑ _b : Fin (k.log2 + 1), A / (64 * cycleFactor k) := Finset.sum_le_sum (fun b _ => hf b)
    _ = (Fintype.card (Fin (k.log2 + 1)) : ℝ) * (A / (64 * cycleFactor k)) := by simp
    _ ≤ (cycleFactor k : ℝ) * (A / (64 * cycleFactor k)) :=
      mul_le_mul_of_nonneg_right (costBatch_count_le k) (div_nonneg hA (by positivity))
    _ = A / 64 := by field_simp

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem first_omissions_family_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (selection : Fin (requests.length.log2 + 1) → Finset (Fin requests.length)) :
    ∑ b, firstOmittedBatchPayment G c requests feasible (selection b) ≤ greedyCost G c requests feasible / 64 := by
  apply finite_bucket_budget
  · rw [← sum_payments_eq_greedyCost G c requests feasible]
    exact Finset.sum_nonneg (fun i _ => payment_nonneg G c hc requests feasible i)
  · intro b
    exact first_omitted_batch_bound G c hc requests feasible (selection b)

theorem long_omissions_family_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (selection : Fin (requests.length.log2 + 1) → Finset (Fin requests.length))
    (hselection : ∀ b, selection b ⊆ costBatch G c requests feasible b) :
    ∑ b, longOmittedBatchPayment G c hc requests feasible fallback (selection b)
      (batchScale G c requests feasible b.val) ≤ greedyCost G c requests feasible / 64 := by
  apply finite_bucket_budget
  · rw [← sum_payments_eq_greedyCost G c requests feasible]
    exact Finset.sum_nonneg (fun i _ => payment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible i)
  · intro b
    apply long_omitted_batch_bound G c hc requests feasible fallback (selection b) (batchScale G c requests feasible b.val)
    intro i hi
    have hb := (costBatch_band G c requests feasible hk ho b i (hselection b hi)).2
    simpa only [blockPayment, dif_pos i.isLt] using le_of_lt hb

end OnlineSteinerForest.UpperBound
