import OnlineSteinerForest.UpperBound.GirthSuppressionBijection

/-! Suppression preserves the degree of every surviving vertex. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem unsuppressDart_tail (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (a : Dart (SuppressedEdge d e)) :
    tail left right (unsuppressDart d e a) =
      (tail (suppressedLeft left right v d e hpair hlabels)
        (suppressedRight left right v d e hpair hlabels) a).val := by
  rcases a with ⟨a, b⟩
  cases a with
  | none =>
    cases b
    · exact tail_reverse left right d
    · exact tail_reverse left right e
  | some i => cases b <;> rfl

theorem suppressed_degree_eq (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1) (x : SuppressedVertex v) :
    degree (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels) x = degree left right x.val := by
  let L := suppressedLeft left right v d e hpair hlabels
  let R := suppressedRight left right v d e hpair hlabels
  have hd : tail left right d = v := by
    have hm : d ∈ outgoing left right v := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2
  have he : tail left right e = v := by
    have hm : e ∈ outgoing left right v := by rw [hpair]; simp
    exact (Finset.mem_filter.mp hm).2
  apply Finset.card_bij (fun a _ => unsuppressDart d e a)
  · intro a ha
    simp only [outgoing, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [unsuppressDart_tail left right v d e hpair hlabels]
    exact congrArg Subtype.val ha
  · intro a _ b _ hab
    exact unsuppressDart_injective d e hlabels hab
  · intro b hb
    have htail : tail left right b = x.val := (Finset.mem_filter.mp hb).2
    have hbd : b ≠ d := by intro h; subst b; exact x.property (htail.symm.trans hd)
    have hbe : b ≠ e := by intro h; subst b; exact x.property (htail.symm.trans he)
    obtain ⟨a, ha⟩ := unsuppressDart_surjective_away d e b hbd hbe
    refine ⟨a, ?_, ha⟩
    simp only [outgoing, Finset.mem_filter, Finset.mem_univ, true_and]
    apply Subtype.ext
    have hh := unsuppressDart_tail left right v d e hpair hlabels a
    rw [ha, htail] at hh
    exact hh.symm

end OnlineSteinerForest.UpperBound.Girth
