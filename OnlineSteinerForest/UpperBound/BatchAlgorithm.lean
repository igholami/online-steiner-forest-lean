import OnlineSteinerForest.UpperBound.BatchDyadicIndex
import OnlineSteinerForest.UpperBound.HistoryPayments
import OnlineSteinerForest.UpperBound.MassParameter

/-! The manuscript's actual low-payment set and finite dyadic cost-batch family. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def dyadicBase (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℝ :=
  optimum G c requests feasible / requests.length

noncomputable def lowPaymentSet (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : Finset (Fin requests.length) :=
  Finset.univ.filter (fun i => payment G c requests feasible i < dyadicBase G c requests feasible)

noncomputable def dyadicBatchIndex (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : Fin requests.length) : ℕ :=
  dyadicFloorIndex (dyadicBase G c requests feasible) (payment G c requests feasible i)

noncomputable def costBatch (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (b : Fin (requests.length.log2 + 1)) : Finset (Fin requests.length) :=
  Finset.univ.filter (fun i => dyadicBase G c requests feasible ≤ payment G c requests feasible i ∧
    dyadicBatchIndex G c requests feasible i = b.val)

noncomputable def batchScale (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (b : ℕ) : ℝ :=
  (2 : ℝ) ^ b * dyadicBase G c requests feasible

theorem dyadicBase_pos (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible) :
    0 < dyadicBase G c requests feasible := div_pos ho (Nat.cast_pos.mpr hk)

theorem costBatch_band (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (b : Fin (requests.length.log2 + 1)) (i : Fin requests.length)
    (hi : i ∈ costBatch G c requests feasible b) :
    batchScale G c requests feasible b.val ≤ payment G c requests feasible i ∧
      payment G c requests feasible i < 2 * batchScale G c requests feasible b.val := by
  have hm := (Finset.mem_filter.mp hi).2
  have hb := dyadic_floor_band _ _ (dyadicBase_pos G c requests feasible hk ho) hm.1
  change (2 : ℝ) ^ dyadicBatchIndex G c requests feasible i * _ ≤ _ ∧ _ < 2 * ((2 : ℝ) ^ dyadicBatchIndex G c requests feasible i * _) at hb
  rw [hm.2] at hb
  exact hb

theorem costBatch_cover (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (hk : 0 < requests.length) (ho : 0 < optimum G c requests feasible)
    (i : Fin requests.length) (hi : i ∉ lowPaymentSet G c requests feasible) :
    ∃ b, i ∈ costBatch G c requests feasible b := by
  have hhigh : dyadicBase G c requests feasible ≤ payment G c requests feasible i := by
    simpa only [lowPaymentSet, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] using hi
  have hbase : (requests.length : ℝ) * dyadicBase G c requests feasible = optimum G c requests feasible := by
    unfold dyadicBase
    have hn : (requests.length : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
    field_simp
  have hupper : payment G c requests feasible i ≤ requests.length * dyadicBase G c requests feasible := by
    rw [hbase]
    exact payment_le_optimum G c hc requests feasible i
  have hindex := dyadic_floor_index_le _ _ requests.length
    (dyadicBase_pos G c requests feasible hk ho) hhigh hk hupper
  exact ⟨⟨dyadicBatchIndex G c requests feasible i, by change dyadicFloorIndex _ _ < _; omega⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hhigh, rfl⟩⟩

theorem costBatch_disjoint (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (b d : Fin (requests.length.log2 + 1)) (hbd : b ≠ d) :
    Disjoint (costBatch G c requests feasible b) (costBatch G c requests feasible d) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hb := (Finset.mem_filter.mp hi).2.2
  have hd := (Finset.mem_filter.mp hj).2.2
  exact hbd (Fin.ext (hb.symm.trans hd))

theorem costBatch_count_le (k : ℕ) : (Fintype.card (Fin (k.log2 + 1)) : ℝ) ≤ cycleFactor k := by
  simpa using log2_add_one_le_cycleFactor k k le_rfl

end OnlineSteinerForest.UpperBound
