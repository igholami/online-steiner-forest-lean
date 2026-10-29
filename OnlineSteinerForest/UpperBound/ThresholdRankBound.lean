import OnlineSteinerForest.UpperBound.GirthSimpleGraph
import OnlineSteinerForest.UpperBound.ChronologyRealCost

/-! Combining actual cycle chronology with the weighted cycle-rank theorem. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {W X I : Type*} [Fintype W] [Fintype I] [DecidableEq W] [DecidableEq I]

theorem rank_mul_separation_le (H : SimpleGraph W) (left right : I → W)
    (hadj : ∀ i, H.Adj (left i) (right i)) (hedges : Function.Injective (fun i => s(left i, right i)))
    (c : Sym2 W → ℝ) (hc : ∀ e, 0 ≤ c e) (hr : 1 ≤ Girth.cycleRank left right)
    (label : Sym2 W → Option ℕ) (hforest : (H.deleteEdges {e | label e ≠ none}).IsAcyclic)
    (hunique : ∀ e f i, label e = some i → label f = some i → e = f)
    (d : ℕ → X → X → ENNReal) (project : W → X)
    (hrefl : ∀ i x, d i x x = 0) (htriangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (τ : ℝ)
    (hseparation : ∀ {a b}, H.Adj a b → ∀ i, label s(a, b) = some i →
      ENNReal.ofReal τ ≤ d i (project a) (project b))
    (hreference : ∀ i {a b}, H.Adj a b → label s(a, b) = none →
      d i (project a) (project b) ≤ ENNReal.ofReal (c s(a, b)))
    (hearlier : ∀ i j {a b}, H.Adj a b → label s(a, b) = some j → j < i →
      d i (project a) (project b) = 0) :
    (Girth.cycleRank left right : ℝ) * τ ≤
      4 * cycleFactor (Girth.cycleRank left right) * (∑ i, c s(left i, right i)) := by
  obtain ⟨z, p, hp, hcost⟩ := Girth.weighted_simple_cycle_rank_bound H left right hadj hedges c hc hr
  have hmetric := cycle_separation_le_cost label hforest hunique d project hrefl htriangle
    (fun e => ENNReal.ofReal (c e)) (ENNReal.ofReal τ) hseparation hreference hearlier p hp
  rw [← ofReal_list_sum_map c hc] at hmetric
  have hnonneg : 0 ≤ (p.edges.map c).sum := List.sum_nonneg (by
    intro x hx
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hx
    exact hc e)
  have hsep : τ ≤ (p.edges.map c).sum := (ENNReal.ofReal_le_ofReal_iff hnonneg).mp hmetric
  have hr' : (0 : ℝ) < Girth.cycleRank left right := by exact_mod_cast hr
  have hh := (le_div_iff₀ hr').mp (hsep.trans hcost)
  simpa only [mul_comm] using hh

end OnlineSteinerForest.UpperBound
