import OnlineSteinerForest.UpperBound.ReferenceCandidate

/-! The actual recursively evolving reference forests for a sequence of future marks. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A state contains its actual original edges and the input-edge invariant. -/
noncomputable def referenceRun (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V) :
    ℕ → {F : Finset (Sym2 V) // ∀ e ∈ F, e ∈ G.edgeSet}
  | 0 => ⟨initial, hinput⟩
  | n + 1 =>
    let state := referenceRun G c hc initial hinput marks n
    ⟨referenceUpdate G c hc state.val state.property (marks n),
      (referenceUpdate_spec G c hc state.val state.property (marks n)).1.1⟩

theorem referenceRun_cost_step (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V) (n : ℕ) :
    edgeCost c (referenceRun G c hc initial hinput marks (n + 1)).val ≤
      edgeCost c (referenceRun G c hc initial hinput marks n).val :=
  referenceUpdate_cost_le G c hc
    (referenceRun G c hc initial hinput marks n).val
    (referenceRun G c hc initial hinput marks n).property (marks n)

theorem referenceRun_cost_le_initial (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V) (n : ℕ) :
    edgeCost c (referenceRun G c hc initial hinput marks n).val ≤ edgeCost c initial := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact (referenceRun_cost_step G c hc initial hinput marks n).trans ih

theorem referenceRun_cost_nonneg (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V) (n : ℕ) :
    0 ≤ edgeCost c (referenceRun G c hc initial hinput marks n).val := by
  apply Finset.sum_nonneg
  intro e he
  exact hc e ((referenceRun G c hc initial hinput marks n).property e he)

end OnlineSteinerForest.UpperBound
