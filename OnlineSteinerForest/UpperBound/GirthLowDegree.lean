import OnlineSteinerForest.UpperBound.GirthConnectedRank
import OnlineSteinerForest.UpperBound.GirthDegreeSum
import OnlineSteinerForest.UpperBound.GirthSuppressionBijection

/-! Low-degree cases of the connected cycle-rank reduction. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem endpoint_isolated_of_outgoing_heads (left right : I → V) (v : V)
    (h : ∀ d ∈ outgoing left right v, head left right d = v) :
    ∀ w, ¬ (endpointGraph left right).Adj v w := by
  intro w hw
  obtain ⟨hne, d, hd, he⟩ := hw
  have hm : d ∈ outgoing left right v := by simp [outgoing, hd]
  exact hne ((h d hm).symm.trans he)

theorem connected_eq_of_isolated {G : SimpleGraph V} (hc : G.Connected) (v : V)
    (hv : ∀ w, ¬ G.Adj v w) (w : V) : v = w := by
  obtain ⟨p⟩ := hc.preconnected v w
  cases p with
  | nil => rfl
  | @cons u z w huz p => exact (hv z huz).elim

theorem degree_zero_rank_zero (left right : I → V) (hc : (endpointGraph left right).Connected)
    (v : V) (hv : degree left right v = 0) : cycleRank left right = 0 := by
  have hempty : outgoing left right v = ∅ := Finset.card_eq_zero.mp hv
  have hiso := endpoint_isolated_of_outgoing_heads left right v (by intro d hd; rw [hempty] at hd; simp at hd)
  have hall := connected_eq_of_isolated hc v hiso
  have hsum : ∑ x, degree left right x = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← hall x, hv]
  rw [degree_sum] at hsum
  have hm : Fintype.card I = 0 := by omega
  have hh := cycleRank_le_edgeCount left right
  omega

theorem degree_two_same_label_isolated (left right : I → V) (v : V) (d e : Dart I)
    (hne : d ≠ e) (hp : outgoing left right v = {d, e}) (hl : d.1 = e.1) :
    ∀ w, ¬ (endpointGraph left right).Adj v w := by
  have he : e = reverse d :=
    (dart_eq_or_reverse_of_label_eq e d hl.symm).resolve_left hne.symm
  have ht : tail left right d = v ∧ tail left right e = v := by
    constructor
    · have hh : d ∈ outgoing left right v := by rw [hp]; simp
      exact (Finset.mem_filter.mp hh).2
    · have hh : e ∈ outgoing left right v := by rw [hp]; simp
      exact (Finset.mem_filter.mp hh).2
  apply endpoint_isolated_of_outgoing_heads left right v
  intro a ha
  rw [hp] at ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rw [he, tail_reverse] at ht
    exact ht.2
  · have hae := Finset.mem_singleton.mp ha
    rw [hae, he, head_reverse]
    exact ht.1

end OnlineSteinerForest.UpperBound.Girth
