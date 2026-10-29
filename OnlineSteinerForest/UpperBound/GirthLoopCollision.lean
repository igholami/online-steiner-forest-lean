import OnlineSteinerForest.UpperBound.GirthCollision
import OnlineSteinerForest.UpperBound.GirthLowDegree
import OnlineSteinerForest.UpperBound.GirthCollapseVertex
import OnlineSteinerForest.UpperBound.FinalParameters

/-! The sole-loop base case of connected graph reduction. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

def loopCollision (left right : I → V) (d : Dart I)
    (hloop : head left right d = tail left right d) : Collision left right where
  start := tail left right d
  finish := tail left right d
  firstTrace := [d]
  secondTrace := []
  firstValid := ⟨rfl, hloop⟩
  secondValid := rfl
  firstNonbacktracking := .singleton d
  secondNonbacktracking := .nil
  distinct := List.cons_ne_nil d []

variable [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem same_label_collision_bound (left right : I → V) (hc : (endpointGraph left right).Connected)
    (v : V) (d e : Dart I) (hne : d ≠ e) (hp : outgoing left right v = {d, e})
    (hl : d.1 = e.1) (hv : degree left right v = 2) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∃ p : Collision left right, p.cost w ≤
      4 * cycleFactor (cycleRank left right) * (∑ i, w i) / cycleRank left right := by
  have hiso := degree_two_same_label_isolated left right v d e hne hp hl
  have hall := connected_eq_of_isolated hc v hiso
  letI : Subsingleton V := ⟨fun x y => (hall x).symm.trans (hall y)⟩
  letI : Nonempty V := ⟨v⟩
  have hvc : Fintype.card V = 1 := by
    simpa only [Nat.card_eq_fintype_card] using (show Nat.card V = 1 from Nat.card_unique)
  have hsum : (∑ x, degree left right x) = 2 := by
    calc
      _ = ∑ _x : V, 2 := Finset.sum_congr rfl (by intro x _; rw [← hall x, hv])
      _ = _ := by simp [hvc]
  rw [degree_sum] at hsum
  have hic : Fintype.card I = 1 := by omega
  have hr : cycleRank left right = 1 := by rw [connected_cycleRank_eq left right hc, hic, hvc]
  have ht := outgoing_pair_tails left right v d e hp
  have her : e = reverse d := (dart_eq_or_reverse_of_label_eq e d hl.symm).resolve_left hne.symm
  have hloop : head left right d = tail left right d := by
    rw [her, tail_reverse] at ht
    exact ht.2.trans ht.1.symm
  let p := loopCollision left right d hloop
  refine ⟨p, ?_⟩
  have hC : 0 ≤ ∑ i, w i := Finset.sum_nonneg (by intro i _; exact hw i)
  have hH : (1 : ℝ) ≤ cycleFactor 1 := by exact_mod_cast cycleFactor_pos 1
  have hsingle : w d.1 ≤ ∑ i, w i := Finset.single_le_sum (by intro i _; exact hw i) (Finset.mem_univ _)
  have hcost : p.cost w = w d.1 := by simp [p, loopCollision, Collision.cost, traceCost]
  rw [hcost, hr]
  simp only [Nat.cast_one, div_one]
  nlinarith

end OnlineSteinerForest.UpperBound.Girth
