import OnlineSteinerForest.UpperBound.OmissionsBatchPayments

/-! Each computed batch loses at most ALG divided by 64 times the pair parameter. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem first_omitted_batch_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (batch : Finset (Fin requests.length)) :
    firstOmittedBatchPayment G c requests feasible batch ≤
      greedyCost G c requests feasible / (64 * cycleFactor requests.length) := by
  have hL : 0 < (cycleFactor requests.length : ℝ) := Nat.cast_pos.mpr (cycleFactor_pos _)
  apply (le_div_iff₀ (by positivity : 0 < (64 : ℝ) * cycleFactor requests.length)).mpr
  apply (mul_le_mul_iff_left₀ hL).mp
  convert first_omitted_batch_scaled G c hc requests feasible batch using 1 <;> ring

theorem long_omitted_batch_bound (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (scale : ℝ)
    (hbatch : ∀ i ∈ batch, blockPayment G c requests feasible i.val ≤ 2 * scale) :
    longOmittedBatchPayment G c hc requests feasible fallback batch scale ≤
      greedyCost G c requests feasible / (64 * cycleFactor requests.length) := by
  have hL : 0 < (cycleFactor requests.length : ℝ) := Nat.cast_pos.mpr (cycleFactor_pos _)
  apply (le_div_iff₀ (by positivity : 0 < (64 : ℝ) * cycleFactor requests.length)).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 2 * (cycleFactor requests.length : ℝ) ^ 2)).mp
  convert long_omitted_batch_scaled G c hc requests feasible fallback batch scale hbatch using 1 <;> ring

end OnlineSteinerForest.UpperBound
