import OnlineSteinerForest.UpperBound.HistorySnapshotForest
import OnlineSteinerForest.UpperBound.MassGreedy

/-! The lifetime-mass bound expressed directly with original input-edge costs. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Sum of the original edge costs of every final live or retired lifetime forest. -/
noncomputable def lifetimeEdgeMass (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) : ℝ :=
  let state := greedyHistory G c requests feasible requests.length
  (state.retired.map (fun C => edgeCost c (clusterEdges G c requests feasible C))).sum +
    ∑ C ∈ state.active, edgeCost c (clusterEdges G c requests feasible C)

theorem lifetimeEdgeMass_eq (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    lifetimeEdgeMass G c requests feasible =
      lifetimeMass (greedyHistory G c requests feasible requests.length)
        (blockPayment G c requests feasible) := by
  unfold lifetimeEdgeMass lifetimeMass
  dsimp only
  apply congrArg₂ (· + ·)
  · congr 1
    apply List.map_congr_left
    intro C hC
    exact clusterEdges_cost G c requests feasible C
      (greedyHistory_snapshot_members G c requests feasible requests.length C (Or.inr hC))
  · apply Finset.sum_congr rfl
    intro C hC
    exact clusterEdges_cost G c requests feasible C
      (greedyHistory_snapshot_members G c requests feasible requests.length C (Or.inl hC))

theorem lifetimeEdgeMass_le (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    lifetimeEdgeMass G c requests feasible ≤
      (((scannedBlocks (fun j => 0 < blockPayment G c requests feasible j)
        requests.length).card.log2 : ℝ) + 1) * greedyCost G c requests feasible := by
  rw [lifetimeEdgeMass_eq]
  exact greedy_lifetime_mass G c hc requests feasible

end OnlineSteinerForest.UpperBound
