import OnlineSteinerForest.UpperBound.ReferenceClassRun

/-! Each computed batch has one canonical residue class and reference forest. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def batchOwner (k : ℕ) (b : Fin (k.log2 + 1)) : Fin (batchClassCount k) :=
  ⟨b.val % batchClassCount k, Nat.mod_lt _ (batchClassCount_pos k)⟩

theorem batch_mem_owner (k : ℕ) (b : Fin (k.log2 + 1)) :
    b ∈ batchClass k (batchOwner k b) :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩

theorem batchOwner_eq (k : ℕ) (r : Fin (batchClassCount k)) (b : Fin (k.log2 + 1))
    (hb : b ∈ batchClass k r) : batchOwner k b = r :=
  Fin.ext (Finset.mem_filter.mp hb).2

noncomputable def batchReference (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (b : Fin (requests.length.log2 + 1)) :
    {F : Finset (Sym2 V) // ∀ e ∈ F, e ∈ G.edgeSet} :=
  classReference G c hc requests feasible (batchOwner requests.length b) b.val

theorem batchReference_eq (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (r : Fin (batchClassCount requests.length)) (b : Fin (requests.length.log2 + 1))
    (hb : b ∈ batchClass requests.length r) :
    batchReference G c hc requests feasible b = classReference G c hc requests feasible r b.val := by
  unfold batchReference
  rw [batchOwner_eq requests.length r b hb]

end OnlineSteinerForest.UpperBound
