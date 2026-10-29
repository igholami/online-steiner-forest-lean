import OnlineSteinerForest.UpperBound.AuxiliaryExtractLabel

/-! Helpful outputs are verified directly in the actual greedy residual metrics. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [Fintype V] [DecidableEq V]

structure HelpfulAt (G : SimpleGraph V) (c : Sym2 V → ℝ) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (scale : ℝ) (out : AuxiliaryOutput V) : Prop where
  path : IsPathEdges G out.left out.right out.edges
  reachable : G.Reachable out.left out.right
  separated : scale / 2 ≤ residualDistance G c (boughtBefore G c requests feasible i.val)
    out.left out.right reachable
  bought_zero : residualDistance G c (boughtBefore G c requests feasible (i.val + 1))
    out.left out.right reachable = 0
  short : edgeCost c out.edges ≤ 256 * (cycleFactor requests.length : ℝ) ^ 3 * scale

theorem direct_scale_bound (L scale pay : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ scale) (hp : pay ≤ 2 * scale) :
    64 * L ^ 2 * pay ≤ 256 * L ^ 3 * scale := by
  have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 64 * L ^ 2)
  have hfac : 128 * L ^ 2 ≤ 256 * L ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have hlast := mul_le_mul_of_nonneg_right hfac hs
  nlinarith

open scoped Classical

theorem directAuxOutput_helpful (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val) (scale : ℝ) (hs : 0 ≤ scale)
    (hlo : scale ≤ payment G c requests feasible i) (hhi : payment G c requests feasible i ≤ 2 * scale)
    (hbranch : isBirth G c requests feasible i.val ∨
      clusterWeight (blockPayment G c requests feasible)
        (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)) ≤
          64 * (cycleFactor requests.length : ℝ) ^ 2 * payment G c requests feasible i) :
    HelpfulAt G c requests feasible i scale (directAuxOutput G c hc requests feasible i hp) := by
  refine ⟨directAuxEdges_spec G c hc requests feasible i hp, feasible _ (List.getElem_mem i.isLt), ?_, ?_, ?_⟩
  · change scale / 2 ≤ payment G c requests feasible i
    have hn := payment_nonneg G c (fun e he => le_of_lt (hc e he)) requests feasible i
    linarith
  · exact residualDistance_eq_zero_of_bought G c (fun e he => le_of_lt (hc e he)) _
      (boughtBefore_input G c requests feasible (i.val + 1)) _ _ _
      (request_reachable_after G c requests feasible i (i.val + 1) (by omega))
  · have hL : 1 ≤ (cycleFactor requests.length : ℝ) := by exact_mod_cast cycleFactor_pos requests.length
    exact (directAuxEdges_cost G c hc requests feasible i hp _ hL hbranch).trans
      (direct_scale_bound _ scale _ hL hs hhi)

end OnlineSteinerForest.UpperBound
