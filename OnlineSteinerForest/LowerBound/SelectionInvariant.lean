import OnlineSteinerForest.Graph.SelectionMetric
import OnlineSteinerForest.LowerBound.RelabelInstance

/-! The lower-bound graph and request sequence are independent of shortest-path ties. -/
namespace OnlineSteinerForest.LowerBound

theorem goodRank_selection_eq (p q : PathSelection.{0}) (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) (i : Fin (matchingSize h)) :
    @GoodRank p h σ i = @GoodRank q h σ i := by
  unfold GoodRank
  rw [residualDistance_selection_eq p q]

theorem retainedRanks_selection_eq (p q : PathSelection.{0}) (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    @retainedRanks p h σ = @retainedRanks q h σ := by
  classical
  unfold retainedRanks
  simp only [goodRank_selection_eq p q]

theorem retainsHalf_selection_eq (p q : PathSelection.{0}) (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    @RetainsHalf p h σ = @RetainsHalf q h σ := by
  unfold RetainsHalf
  rw [retainedRanks_selection_eq p q]

theorem instanceGraph_selection_eq (p q : PathSelection.{0}) (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    @instanceGraph p h σ = @instanceGraph q h σ := by
  unfold instanceGraph
  rw [retainedRanks_selection_eq p q]

theorem instanceRequests_selection_eq (p q : PathSelection.{0}) (h : ℕ)
    (σ : Equiv.Perm (Fin (2 * matchingSize h))) :
    @instanceRequests p h σ = @instanceRequests q h σ := by
  unfold instanceRequests
  rw [retainedRanks_selection_eq p q]

theorem relabelInstanceGraph_selection_eq {W : Type} [Fintype W] [DecidableEq W]
    (p q : PathSelection.{0}) (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) :
    (letI := p; relabelInstanceGraph h σ e) =
      (letI := q; relabelInstanceGraph h σ e) := by
  unfold relabelInstanceGraph
  rw [instanceGraph_selection_eq p q]

theorem relabelInstanceRequests_selection_eq {W : Type} [Fintype W] [DecidableEq W]
    (p q : PathSelection.{0}) (h : ℕ) (σ : Equiv.Perm (Fin (2 * matchingSize h)))
    (e : Vertex (matchingSize h) ≃ W) :
    (letI := p; relabelInstanceRequests h σ e) =
      (letI := q; relabelInstanceRequests h σ e) := by
  unfold relabelInstanceRequests
  rw [instanceRequests_selection_eq p q]

/-- Equality of input data also transports the dependent feasibility witness. -/
theorem greedyCost_input_eq [PathSelection.{0}] {V : Type} [Fintype V] [DecidableEq V]
    {G G' : SimpleGraph V} {c : Sym2 V → ℝ} {rs rs' : List (V × V)}
    (hG : G = G') (hrs : rs = rs')
    (hf : ∀ q ∈ rs, G.Reachable q.1 q.2)
    (hf' : ∀ q ∈ rs', G'.Reachable q.1 q.2) :
    greedyCost G c rs hf = greedyCost G' c rs' hf' := by
  subst G'
  subst rs'
  rfl

end OnlineSteinerForest.LowerBound
