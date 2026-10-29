import OnlineSteinerForest.UpperBound.GirthSubdivision

/-! Nonbacktracking labelled walks stay nonbacktracking in the simple subdivision. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

theorem dartWalk_chain (left right : I → V) (d : Dart I) :
    List.IsChain (· ≠ ·) (dartWalk left right d).edges := by
  simp [dartWalk_edges, List.isChain_cons_cons, Sym2.eq_iff]

theorem subdividedWalk_last_edge (left right : I → V) (n : ℕ) (p : Paths (Dart I) n)
    (hp : Nonbacktracking left right n p) :
    (subdividedWalk left right n p hp).edges.getLast? =
      some s(.inr (reverse (last n p)), .inl (head left right (last n p))) := by
  cases n with
  | zero =>
    change Dart I at p
    change (dartWalk left right p).edges.getLast? = _
    rw [dartWalk_edges]
    rfl
  | succ n =>
    change Paths (Dart I) n × Dart I at p
    change Nonbacktracking left right n p.1 ∧ p.2 ∈ successors left right (last n p.1) at hp
    change ((subdividedWalk left right n p.1 hp.1).append
      ((dartWalk left right p.2).copy _ _)).edges.getLast? = _
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy, dartWalk_edges]
    simp [last]

theorem subdividedWalk_chain (left right : I → V) (n : ℕ) (p : Paths (Dart I) n)
    (hp : Nonbacktracking left right n p) :
    List.IsChain (· ≠ ·) (subdividedWalk left right n p hp).edges := by
  induction n with
  | zero =>
    change Dart I at p
    exact dartWalk_chain left right p
  | succ n ih =>
    change Paths (Dart I) n × Dart I at p
    change Nonbacktracking left right n p.1 ∧ p.2 ∈ successors left right (last n p.1) at hp
    change List.IsChain (· ≠ ·) ((subdividedWalk left right n p.1 hp.1).append
      ((dartWalk left right p.2).copy _ _)).edges
    rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_copy]
    apply (ih p.1 hp.1).append (dartWalk_chain left right p.2)
    intro e he f hf
    rw [subdividedWalk_last_edge] at he
    simp only [Option.mem_def, Option.some.injEq] at he
    simp only [dartWalk_edges, List.head?_cons, Option.mem_def, Option.some.injEq] at hf
    subst e
    subst f
    have hne := (Finset.mem_erase.mp hp.2).1
    simp only [ne_eq, Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, and_false, false_and, or_false, not_and]
    intro hd
    rcases hd with hd | ⟨hd, _⟩
    · exact hd.elim
    · exact hne hd.symm

end OnlineSteinerForest.UpperBound.Girth
