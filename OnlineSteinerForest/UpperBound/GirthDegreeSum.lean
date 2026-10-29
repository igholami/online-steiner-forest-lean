import OnlineSteinerForest.UpperBound.GirthTransition

/-! The handshake identity for labelled loops and parallel edges. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

theorem degree_sum (left right : I → V) :
    (∑ v, degree left right v) = 2 * Fintype.card I := by
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Dart I)) (Finset.univ : Finset V) (tail left right)
  simpa [degree, outgoing, Dart, Fintype.card_prod, Nat.mul_comm] using hh

theorem minimum_degree_vertex_bound (left right : I → V)
    (hdegree : ∀ v, 3 ≤ degree left right v) (r components : ℕ)
    (hrank : Fintype.card I + components = Fintype.card V + r) :
    Fintype.card V ≤ 2 * r := by
  have hh : 3 * Fintype.card V ≤ 2 * Fintype.card I := by
    calc
      _ = ∑ _v : V, 3 := by simp [Nat.mul_comm]
      _ ≤ ∑ v, degree left right v := Finset.sum_le_sum (by intro v _; exact hdegree v)
      _ = _ := degree_sum left right
  omega

end OnlineSteinerForest.UpperBound.Girth
