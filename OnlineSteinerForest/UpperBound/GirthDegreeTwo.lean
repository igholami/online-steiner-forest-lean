import OnlineSteinerForest.UpperBound.GirthDarts

/-! Identifying the two incident labelled edges before suppressing a degree-two vertex. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem degree_two_outgoing (left right : I → V) (v : V) (hv : degree left right v = 2) :
    ∃ d e : Dart I, d ≠ e ∧ outgoing left right v = {d, e} := by
  exact Finset.card_eq_two.mp hv

theorem reverse_ne_self (d : Dart I) : reverse d ≠ d := by
  rcases d with ⟨i, b⟩
  cases b <;> simp [reverse]

theorem outgoing_pair_nonloop (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) :
    head left right d ≠ v ∧ head left right e ≠ v := by
  have hleft : ∀ a b : Dart I, outgoing left right v = {a, b} → a.1 ≠ b.1 → head left right a ≠ v := by
    intro a b hp hab hhead
    have hr : reverse a ∈ outgoing left right v := by
      simp only [outgoing, Finset.mem_filter, Finset.mem_univ, true_and, tail_reverse]
      exact hhead
    rw [hp] at hr
    rcases Finset.mem_insert.mp hr with hr | hr
    · exact reverse_ne_self a hr
    · have hh := congrArg Prod.fst (Finset.mem_singleton.mp hr)
      exact hab hh
  exact ⟨hleft d e hpair hlabels, hleft e d (by simpa [Finset.pair_comm] using hpair) hlabels.symm⟩

theorem remaining_edge_avoids_vertex (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (i : I) (hi₁ : i ≠ d.1) (hi₂ : i ≠ e.1) :
    left i ≠ v ∧ right i ≠ v := by
  have hh : ∀ b : Bool, tail left right (i, b) ≠ v := by
    intro b h
    have hm : (i, b) ∈ outgoing left right v := by simp [outgoing, h]
    rw [hpair] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact hi₁ (congrArg Prod.fst hm)
    · exact hi₂ (congrArg Prod.fst (Finset.mem_singleton.mp hm))
  exact ⟨hh false, hh true⟩

end OnlineSteinerForest.UpperBound.Girth
