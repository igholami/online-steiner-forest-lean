import OnlineSteinerForest.UpperBound.HistoryPersistence
import OnlineSteinerForest.UpperBound.HistoryBlocks

/-! Label persistence expressed in the original purchased graph edges. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem clusterEdges_mono_members (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (C D : LabeledCluster ℕ) (hCD : C.members ⊆ D.members) :
    clusterEdges G c requests feasible C ⊆ clusterEdges G c requests feasible D := by
  intro e he
  obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
  exact Finset.mem_biUnion.mpr ⟨j, hCD hj, he⟩

/-- A current component's purchased edges remain in a final lifetime forest with
that same label, even if its component subsequently retires. -/
theorem greedyHistory_lifetime_contains (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i j : ℕ) (hij : i ≤ j) (C : LabeledCluster ℕ)
    (hC : IsSnapshot (greedyHistory G c requests feasible i) C) :
    ∃ D, IsSnapshot (greedyHistory G c requests feasible j) D ∧ D.label = C.label ∧
      clusterEdges G c requests feasible C ⊆ clusterEdges G c requests feasible D := by
  obtain ⟨D, hD, hl, hs⟩ := scanHistory_persists
    (fun k => 0 < blockPayment G c requests feasible k) (touchesBlock G c requests feasible) i j hij C hC
  exact ⟨D, hD, hl, clusterEdges_mono_members G c requests feasible C D hs⟩

end OnlineSteinerForest.UpperBound
