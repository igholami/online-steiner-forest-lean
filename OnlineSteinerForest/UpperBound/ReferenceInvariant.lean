import OnlineSteinerForest.UpperBound.ReferenceRun

/-! Decreasing future-mark sets maintain the reference connection invariant. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Each update preserves a pair if both endpoints were marked at that update. -/
theorem referenceRun_preserves_each (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V)
    (n : ℕ) {u v : V} (hu : ∀ i < n, u ∈ marks i) (hv : ∀ i < n, v ∈ marks i)
    (hr : (SimpleGraph.fromEdgeSet (initial : Set (Sym2 V))).Reachable u v) :
    (SimpleGraph.fromEdgeSet (((referenceRun G c hc initial hinput marks n).val :
      Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    exact referenceUpdate_preserves G c hc
      (referenceRun G c hc initial hinput marks n).val
      (referenceRun G c hc initial hinput marks n).property (marks n) (hu n (Nat.lt_succ_self n))
      (hv n (Nat.lt_succ_self n))
      (ih (fun i hi => hu i (Nat.lt.step hi)) (fun i hi => hv i (Nat.lt.step hi)))

theorem referenceRun_preserves_future (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (initial : Finset (Sym2 V))
    (hinput : ∀ e ∈ initial, e ∈ G.edgeSet) (marks : ℕ → Finset V)
    (hmarks : Antitone marks) (n : ℕ) {u v : V}
    (hu : u ∈ marks n) (hv : v ∈ marks n)
    (hr : (SimpleGraph.fromEdgeSet (initial : Set (Sym2 V))).Reachable u v) :
    (SimpleGraph.fromEdgeSet (((referenceRun G c hc initial hinput marks n).val :
      Finset (Sym2 V)) : Set (Sym2 V))).Reachable u v := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    have hu' := hmarks (Nat.le_succ n) hu
    have hv' := hmarks (Nat.le_succ n) hv
    exact referenceUpdate_preserves G c hc
      (referenceRun G c hc initial hinput marks n).val
      (referenceRun G c hc initial hinput marks n).property (marks n) hu' hv' (ih hu' hv')

end OnlineSteinerForest.UpperBound
