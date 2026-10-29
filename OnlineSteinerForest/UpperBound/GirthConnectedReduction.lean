import OnlineSteinerForest.UpperBound.GirthKernelCollision
import OnlineSteinerForest.UpperBound.GirthPruneLeafRank
import OnlineSteinerForest.UpperBound.GirthPruneLeafCollision
import OnlineSteinerForest.UpperBound.GirthSuppressionRank
import OnlineSteinerForest.UpperBound.GirthSuppressionConnected
import OnlineSteinerForest.UpperBound.GirthSuppressionCollision
import OnlineSteinerForest.UpperBound.GirthSuppressionCost
import OnlineSteinerForest.UpperBound.GirthLoopCollision
import Mathlib.Tactic.GCongr

/-! Connected weighted cycle-rank bound by actual leaf deletion and degree-two suppression. -/
namespace OnlineSteinerForest.UpperBound.Girth

universe u v

theorem connected_collision_bound_aux (n : ℕ) :
    ∀ (V : Type u) (I : Type v) [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
      (left right : I → V) (w : I → ℝ), (∀ i, 0 ≤ w i) → Fintype.card V = n →
      (endpointGraph left right).Connected → 1 ≤ cycleRank left right →
      ∃ p : Collision left right, p.cost w ≤
        4 * cycleFactor (cycleRank left right) * (∑ i, w i) / cycleRank left right := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V I _ _ _ _ left right w hw hcard hc hr
    have hm := cycleRank_le_edgeCount left right
    letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
    by_cases hmin : ∀ x, 3 ≤ degree left right x
    · exact kernel_collision_rank_bound left right hmin w hw hr
    · push_neg at hmin
      obtain ⟨x, hx⟩ := hmin
      have hcases : degree left right x = 0 ∨ degree left right x = 1 ∨ degree left right x = 2 := by omega
      rcases hcases with hzero | hone | htwo
      · have hz := degree_zero_rank_zero left right hc x hzero
        omega
      · obtain ⟨d, hd⟩ := degree_one_outgoing left right x hone
        have hsmall : Fintype.card (SuppressedVertex x) < n := by
          have hv := suppressedVertex_card x
          omega
        have hconn := leaf_endpoint_connected left right x d hd hc
        have hR := leaf_cycleRank left right x d hd hc
        obtain ⟨p, hp⟩ := ih (Fintype.card (SuppressedVertex x)) hsmall
          (SuppressedVertex x) (PrunedLeafEdge d) (leafLeft left right x d hd)
          (leafRight left right x d hd) (fun i => w i.val) (by intro i; exact hw i.val)
          rfl hconn (by rw [hR]; exact hr)
        refine ⟨liftLeafCollision left right x d hd p, ?_⟩
        rw [liftLeafCollision_cost]
        refine hp.trans ?_
        rw [hR]
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (leaf_weight_sum_le w hw d) (by positivity)) (by positivity)
      · obtain ⟨d, e, hne, hpair⟩ := degree_two_outgoing left right x htwo
        by_cases hl : d.1 = e.1
        · exact same_label_collision_bound left right hc x d e hne hpair hl htwo w hw
        · have hsmall : Fintype.card (SuppressedVertex x) < n := by
            have hv := suppressedVertex_card x
            omega
          have hconn := suppressed_endpoint_connected left right x d e hpair hl hc
          have hR := suppressed_cycleRank left right x d e hpair hl
          obtain ⟨p, hp⟩ := ih (Fintype.card (SuppressedVertex x)) hsmall
            (SuppressedVertex x) (SuppressedEdge d e) (suppressedLeft left right x d e hpair hl)
            (suppressedRight left right x d e hpair hl) (suppressedWeight w d e)
            (suppressedWeight_nonneg w hw d e) rfl hconn (by rw [hR]; exact hr)
          refine ⟨expandCollision left right x d e hpair hl p, ?_⟩
          rw [expandCollision_cost]
          simpa only [suppressedWeight_sum w d e hl, hR] using hp

theorem connected_collision_bound {V : Type u} {I : Type v} [Fintype V] [Fintype I]
    [DecidableEq V] [DecidableEq I] (left right : I → V) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hc : (endpointGraph left right).Connected) (hr : 1 ≤ cycleRank left right) :
    ∃ p : Collision left right, p.cost w ≤
      4 * cycleFactor (cycleRank left right) * (∑ i, w i) / cycleRank left right :=
  connected_collision_bound_aux (Fintype.card V) V I left right w hw rfl hc hr

end OnlineSteinerForest.UpperBound.Girth
