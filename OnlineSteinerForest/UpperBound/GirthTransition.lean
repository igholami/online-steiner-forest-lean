import OnlineSteinerForest.UpperBound.GirthDarts
import OnlineSteinerForest.Graph.Cost
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-! Uniform orientations are stationary for the nonbacktracking transition kernel. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

noncomputable def transition (left right : I → V) (d e : Dart I) : ℝ :=
  if e ∈ successors left right d then (1 : ℝ) / (successors left right d).card else 0

theorem transition_nonneg (left right : I → V) (d e : Dart I) : 0 ≤ transition left right d e := by
  unfold transition
  split_ifs <;> positivity

theorem transition_row_sum (left right : I → V) (hdegree : ∀ v, 3 ≤ degree left right v)
    (d : Dart I) : (∑ e : Dart I, transition left right d e) = 1 := by
  have hcard : 0 < (successors left right d).card := by
    have hd := hdegree (head left right d)
    rw [successors_card]
    omega
  unfold transition
  rw [← Finset.sum_filter]
  have hf : (Finset.univ.filter fun e => e ∈ successors left right d) = successors left right d := by
    ext e
    simp
  rw [hf]
  simp [nsmul_eq_mul, Nat.cast_ne_zero.mpr hcard.ne']

theorem transition_as_predecessor (left right : I → V) (d e : Dart I) :
    transition left right d e = if d ∈ predecessors left right e then
      (1 : ℝ) / (predecessors left right e).card else 0 := by
  by_cases h : e ∈ successors left right d
  · have hpred := (mem_successors_iff_mem_predecessors left right d e).mp h
    have hv : head left right d = tail left right e := by
      have hh := (Finset.mem_erase.mp h).2
      exact (Finset.mem_filter.mp hh).2.symm
    simp only [transition, h, hpred, ↓reduceIte, successors_card, predecessors_card, hv]
  · have hpred : d ∉ predecessors left right e :=
      fun hp => h ((mem_successors_iff_mem_predecessors left right d e).mpr hp)
    simp [transition, h, hpred]

theorem transition_column_sum (left right : I → V) (hdegree : ∀ v, 3 ≤ degree left right v)
    (e : Dart I) : (∑ d : Dart I, transition left right d e) = 1 := by
  have hcard : 0 < (predecessors left right e).card := by
    have hd := hdegree (tail left right e)
    rw [predecessors_card]
    omega
  simp_rw [transition_as_predecessor]
  rw [← Finset.sum_filter]
  have hf : (Finset.univ.filter fun d => d ∈ predecessors left right e) = predecessors left right e := by
    ext d
    simp
  rw [hf]
  simp [nsmul_eq_mul, Nat.cast_ne_zero.mpr hcard.ne']

theorem transition_le_half (left right : I → V) (hdegree : ∀ v, 3 ≤ degree left right v)
    (d e : Dart I) : transition left right d e ≤ 1 / 2 := by
  have hcard : 2 ≤ (successors left right d).card := by
    have hd := hdegree (head left right d)
    rw [successors_card]
    omega
  unfold transition
  split_ifs
  · exact one_div_le_one_div_of_le (by norm_num) (Nat.cast_le.mpr hcard)
  · norm_num

end OnlineSteinerForest.UpperBound.Girth
