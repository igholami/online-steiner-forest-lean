import OnlineSteinerForest.UpperBound.SparseDiscard
import OnlineSteinerForest.UpperBound.SparseParameterBudget

/-! The actual peeling algorithm satisfies the exact discarded-payment count bound. -/
namespace OnlineSteinerForest.UpperBound

variable {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]

theorem configured_discarded_count_scale_le (L : ℕ) (hL : 1 ≤ L) (left right : I → V)
    (S : Finset V) (hleft : ∀ i, left i ∈ S) (hright : ∀ i, right i ∈ S)
    (hloops : ∀ v ∈ S, (loopsAt left right v).card ≤ parallelCap L)
    (scale C : ℝ) (hscale : 0 ≤ scale)
    (hzones : (S.card : ℝ) * zoneMultiplier L * scale ≤ C) :
    ((Fintype.card I - (liveEdges left right (sparseCore left right (coreDegree L) S)).card : ℕ) : ℝ) * scale ≤
      (2 : ℝ) ^ 28 * cycleFactor L * C := by
  exact discarded_count_scale_le L S.card _ hL scale C hscale
    (discarded_edges_le left right S (parallelCap L) (coreDegree L) hleft hright hloops) hzones

end OnlineSteinerForest.UpperBound
