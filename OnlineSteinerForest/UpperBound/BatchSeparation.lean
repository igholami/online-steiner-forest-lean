import OnlineSteinerForest.UpperBound.BatchClasses

/-! Consecutive processed buckets in a residue class have the required exponential scale gap. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem batchScale_pos (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) (b : ℕ) :
    0 < batchScale G c requests feasible b :=
  mul_pos (pow_pos (by norm_num) _) (dyadicBase_pos G c requests feasible hk ho)

theorem batchScale_ratio (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (b d : ℕ) (hbd : b ≤ d) :
    batchScale G c requests feasible d = (2 : ℝ) ^ (d - b) * batchScale G c requests feasible b := by
  unfold batchScale
  have hp : (2 : ℝ) ^ d = (2 : ℝ) ^ (d - b) * (2 : ℝ) ^ b := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  ring

theorem batchClass_scale_gap (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (r : Fin (batchClassCount requests.length)) (b d : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r) (hd : d ∈ batchClass requests.length r) (hbd : b.val < d.val) :
    (2 : ℝ) ^ batchClassCount requests.length * batchScale G c requests feasible b.val ≤
      batchScale G c requests feasible d.val := by
  rw [batchScale_ratio G c requests feasible b.val d.val hbd.le]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) (batchClass_gap requests.length r b d hb hd hbd))
    (le_of_lt (batchScale_pos G c requests feasible hk ho b.val))

end OnlineSteinerForest.UpperBound
