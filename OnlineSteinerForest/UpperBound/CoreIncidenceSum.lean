import OnlineSteinerForest.UpperBound.SparseCore
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! The actual loopless labelled core satisfies the degree-sum formula. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

variable {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]

theorem sum_incidentEdges_card (left right : I → V) (S : Finset V) :
    (∑ v ∈ S, (incidentEdges left right S v).card) = 2 * (liveEdges left right S).card := by
  let E := liveEdges left right S
  have hsplit (v : V) : (incidentEdges left right S v).card =
      (E.filter fun i => left i = v).card + (E.filter fun i => right i = v).card := by
    have hd : Disjoint (E.filter fun i => left i = v) (E.filter fun i => right i = v) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.2.2
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm)
    rw [← Finset.card_union_of_disjoint hd]
    congr 1
    ext i
    simp only [incidentEdges, E, Finset.mem_filter, Finset.mem_union, and_or_left]
  have hleft : (∑ v ∈ S, (E.filter fun i => left i = v).card) = E.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr fun i hi => (Finset.mem_filter.mp hi).2.1
  have hright : (∑ v ∈ S, (E.filter fun i => right i = v).card) = E.card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_eq_self.mpr fun i hi => (Finset.mem_filter.mp hi).2.2.1
  calc
    _ = ∑ v ∈ S, ((E.filter fun i => left i = v).card +
        (E.filter fun i => right i = v).card) := Finset.sum_congr rfl (fun v _ => hsplit v)
    _ = (∑ v ∈ S, (E.filter fun i => left i = v).card) +
        (∑ v ∈ S, (E.filter fun i => right i = v).card) := Finset.sum_add_distrib
    _ = E.card + E.card := congrArg₂ (· + ·) hleft hright
    _ = 2 * E.card := by omega

theorem core_vertices_le_half_edges (left right : I → V) (S : Finset V)
    (hmin : ∀ v ∈ S, 4 ≤ (incidentEdges left right S v).card) :
    2 * S.card ≤ (liveEdges left right S).card := by
  have hsum := Finset.sum_le_sum hmin
  rw [sum_incidentEdges_card] at hsum
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hsum
  omega

end OnlineSteinerForest.UpperBound
