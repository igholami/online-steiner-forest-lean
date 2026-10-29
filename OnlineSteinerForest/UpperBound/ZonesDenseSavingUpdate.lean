import OnlineSteinerForest.UpperBound.ZonesDenseSaving
import OnlineSteinerForest.UpperBound.ReferenceCandidate

/-! The concrete dense replacement saves at least as much under the actual canonical reference update. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

theorem dense_referenceUpdate_saving (core : SimpleGraph V) (ambient : SimpleGraph W)
    (hdeg : ∀ v, 8191 ≤ core.degree v) (zones : V → Finset (Sym2 W)) (old : Finset (Sym2 W))
    (marks : Finset W) (c : Sym2 W → ℝ) (M : ℝ) (hM : 0 < M)
    (hc : ∀ e ∈ ambient.edgeSet, 0 ≤ c e) (hold : ∀ e ∈ old, e ∈ ambient.edgeSet)
    (hsub : ∀ v, zones v ⊆ old) (hdis : (↑(Finset.univ : Finset V) : Set V).PairwiseDisjoint zones)
    (hlower : ∀ v, M ≤ edgeCost c (zones v)) (hupper : ∀ v, edgeCost c (zones v) ≤ 3 * M)
    (hconn : ∀ v, ZoneConnected (zones v))
    (hreal : ∀ u v, core.Adj u v → ∃ a b : W, ∃ P : Finset (Sym2 W),
      zoneSupport (zones u) a ∧ zoneSupport (zones v) b ∧
        IsPathEdges ambient a b P ∧ edgeCost c P ≤ M / 256) :
    edgeCost c (zoneCoreEdges zones) / 2 - 8 * M * marks.card ≤
      edgeCost c old - edgeCost c (referenceUpdate ambient c hc old hold marks) := by
  obtain ⟨C, hC, hcost, hmarks⟩ := exists_dense_replacement_candidate core ambient hdeg zones old marks
    c M hM hc hold hsub hdis hlower hupper hconn hreal
  have hupdate := referenceUpdate_cost_le_candidate ambient c hc old hold marks C hC hmarks
  linarith

end OnlineSteinerForest.UpperBound
