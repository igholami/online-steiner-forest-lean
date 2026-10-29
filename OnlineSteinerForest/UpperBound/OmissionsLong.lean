import OnlineSteinerForest.UpperBound.NearestNeighbor
import Mathlib.Tactic.Linarith

/-! The long-proxy omission estimate uses the implemented nearest-earlier choice. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def longProxyIndices (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hconn : G.Preconnected) {n : ℕ} (x : Fin (n + 1) → V) (L scale : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 256 * L ^ 3 * scale < insertionDistance G c hconn x i)

/-- Across one lifetime tree, long proxy lengths have the full nearest-neighbor budget. -/
theorem long_proxy_lengths (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) {n : ℕ} (x : Fin (n + 1) → V) (L scale : ℝ) :
    ∑ i ∈ longProxyIndices G c hG.connected.preconnected x L scale,
      insertionDistance G c hG.connected.preconnected x i ≤
        2 * edgeCost c G.edgeFinset * Real.log ((n + 1 : ℕ) : ℝ) := by
  apply le_trans _ (nearest_neighbor_sum G hG c hc x)
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
  intro i hi hnot
  exact insertionDistance_nonneg G c hc hG.connected.preconnected x i

/-- Every long omitted payment is bounded by its actual proxy length, and the
sum is controlled by the tree's proved nearest-neighbor estimate. -/
theorem long_proxy_payments (G : SimpleGraph V) (hG : G.IsTree) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 ≤ c e) {n : ℕ} (x : Fin (n + 1) → V)
    (L scale : ℝ) (hL : 0 ≤ L) (pay : Fin n → ℝ) (hpay : ∀ i, pay i ≤ 2 * scale) :
    (128 * L ^ 3) * ∑ i ∈ longProxyIndices G c hG.connected.preconnected x L scale, pay i ≤
      2 * edgeCost c G.edgeFinset * Real.log ((n + 1 : ℕ) : ℝ) := by
  apply le_trans _ (long_proxy_lengths G hG c hc x L scale)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hdist := (Finset.mem_filter.mp hi).2
  have hmul := mul_le_mul_of_nonneg_left (hpay i) (by positivity : 0 ≤ 128 * L ^ 3)
  nlinarith

end OnlineSteinerForest.UpperBound
