import OnlineSteinerForest.UpperBound.BatchPaymentSums
import Mathlib.Data.Nat.ModEq

/-! Compute separated residue classes and choose a maximum-payment class. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem batchClassCount_pos (k : ℕ) : 0 < batchClassCount k := by
  unfold batchClassCount
  omega

noncomputable def batchClass (k : ℕ) (r : Fin (batchClassCount k)) : Finset (Fin (k.log2 + 1)) :=
  Finset.univ.filter (fun b => b.val % batchClassCount k = r.val)

noncomputable def batchClassPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) : ℝ :=
  ∑ b ∈ batchClass requests.length r, ∑ i ∈ costBatch G c requests feasible b, payment G c requests feasible i

noncomputable def selectedBatchClass (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    Fin (batchClassCount requests.length) :=
  Classical.choose ((Finset.univ : Finset (Fin (batchClassCount requests.length))).exists_max_image
    (batchClassPayment G c requests feasible) ⟨⟨0, batchClassCount_pos _⟩, Finset.mem_univ _⟩)

theorem selectedBatchClass_max (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) :
    batchClassPayment G c requests feasible r ≤
      batchClassPayment G c requests feasible (selectedBatchClass G c requests feasible) :=
  (Classical.choose_spec ((Finset.univ : Finset (Fin (batchClassCount requests.length))).exists_max_image
    (batchClassPayment G c requests feasible) ⟨⟨0, batchClassCount_pos _⟩, Finset.mem_univ _⟩)).2 r (Finset.mem_univ _)

theorem batchClass_union (k : ℕ) : Finset.univ.biUnion (batchClass k) = Finset.univ := by
  apply Finset.Subset.antisymm (Finset.subset_univ _)
  intro b hb
  refine Finset.mem_biUnion.mpr ⟨⟨b.val % batchClassCount k, Nat.mod_lt _ (batchClassCount_pos k)⟩,
    Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩

theorem batchClass_disjoint (k : ℕ) (r s : Fin (batchClassCount k)) (hrs : r ≠ s) :
    Disjoint (batchClass k r) (batchClass k s) := by
  apply Finset.disjoint_left.mpr
  intro b hb hs
  exact hrs (Fin.ext ((Finset.mem_filter.mp hb).2.symm.trans (Finset.mem_filter.mp hs).2))

theorem batchClass_gap (k : ℕ) (r : Fin (batchClassCount k))
    (b d : Fin (k.log2 + 1)) (hb : b ∈ batchClass k r) (hd : d ∈ batchClass k r) (hbd : b.val < d.val) :
    batchClassCount k ≤ d.val - b.val := by
  have hmod : b.val ≡ d.val [MOD batchClassCount k] :=
    (Finset.mem_filter.mp hb).2.trans (Finset.mem_filter.mp hd).2.symm
  exact Nat.le_of_dvd (Nat.sub_pos_of_lt hbd) ((Nat.modEq_iff_dvd' hbd.le).mp hmod)

theorem sum_batchClassPayment (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    ∑ r : Fin (batchClassCount requests.length), batchClassPayment G c requests feasible r =
      ∑ b : Fin (requests.length.log2 + 1), ∑ i ∈ costBatch G c requests feasible b, payment G c requests feasible i := by
  unfold batchClassPayment
  rw [← Finset.sum_biUnion (fun r hr s hs hrs => batchClass_disjoint _ r s hrs), batchClass_union]

end OnlineSteinerForest.UpperBound
