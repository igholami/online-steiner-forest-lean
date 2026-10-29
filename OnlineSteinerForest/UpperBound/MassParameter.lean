import OnlineSteinerForest.UpperBound.MassGreedyEdges
import OnlineSteinerForest.UpperBound.FinalParameters

/-! Convert the union-by-size count bound to the manuscript's logarithmic parameter. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

theorem log2_add_one_le_cycleFactor (r n : ℕ) (hrn : r ≤ n) :
    (r.log2 : ℝ) + 1 ≤ cycleFactor n := by
  by_cases hr : r = 0
  · subst r
    exact_mod_cast cycleFactor_pos n
  · have hn : 0 < n := (Nat.pos_of_ne_zero hr).trans_le hrn
    have hp : (2 : ℝ) ^ r.log2 ≤ 8 * (n : ℝ) := by
      have hp' : (2 : ℝ) ^ r.log2 ≤ (r : ℝ) := by exact_mod_cast Nat.log2_self_le hr
      have hrn' : (r : ℝ) ≤ n := Nat.cast_le.mpr hrn
      nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have hl := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ r.log2) hp
    rw [Real.log_pow] at hl
    have hdiv : (r.log2 : ℝ) ≤ Real.logb 2 (8 * (n : ℝ)) := by
      rw [Real.logb]
      exact (le_div_iff₀ log_two_pos).mpr hl
    have hceil := (Nat.le_ceil (Real.logb 2 (8 * (n : ℝ))))
    have htot := hdiv.trans hceil
    simpa [cycleFactor, Nat.cast_add, Nat.cast_one] using add_le_add htot (le_refl (1 : ℝ))

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Manuscript lifetime-mass inequality for the implemented persistent labels. -/
theorem lifetimeEdgeMass_le_pairLog (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) :
    lifetimeEdgeMass G c requests feasible ≤
      cycleFactor requests.length * greedyCost G c requests feasible := by
  apply (lifetimeEdgeMass_le G c hc requests feasible).trans
  apply mul_le_mul_of_nonneg_right
  · apply log2_add_one_le_cycleFactor
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  · rw [← sum_payments_eq_greedyCost G c requests feasible]
    exact Finset.sum_nonneg (fun i _ => payment_nonneg G c hc requests feasible i)

end OnlineSteinerForest.UpperBound
