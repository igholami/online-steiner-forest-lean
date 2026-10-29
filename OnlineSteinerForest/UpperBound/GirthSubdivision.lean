import OnlineSteinerForest.UpperBound.GirthDartPaths
import OnlineSteinerForest.UpperBound.GirthCycleSupport

/-! A standard simple-graph subdivision preserving labelled loops and parallel edges. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

def edgeSubdivision (left right : I → V) : SimpleGraph (V ⊕ Dart I) where
  Adj a b := match a, b with
    | .inl v, .inl _ => False
    | .inl v, .inr d => v = tail left right d
    | .inr d, .inl v => v = tail left right d
    | .inr d, .inr e => e = reverse d
  symm.symm a b := by
    intro h
    cases a with
    | inl v => cases b <;> exact h
    | inr d =>
      cases b with
      | inl v => exact h
      | inr e =>
        change d = reverse e
        simpa using (congrArg reverse h).symm
  loopless.irrefl a := by
    intro h
    cases a with
    | inl v => exact h
    | inr d =>
      rcases d with ⟨i, b⟩
      cases b <;> cases h

def dartWalk (left right : I → V) (d : Dart I) :
    (edgeSubdivision left right).Walk (.inl (tail left right d)) (.inl (head left right d)) :=
  .cons (show (edgeSubdivision left right).Adj (.inl (tail left right d)) (.inr d) from rfl)
    (.cons (show (edgeSubdivision left right).Adj (.inr d) (.inr (reverse d)) from rfl)
      (.cons (show (edgeSubdivision left right).Adj (.inr (reverse d)) (.inl (head left right d))
        from (tail_reverse left right d).symm) .nil))

@[simp] theorem dartWalk_support (left right : I → V) (d : Dart I) :
    (dartWalk left right d).support =
      [.inl (tail left right d), .inr d, .inr (reverse d), .inl (head left right d)] := rfl

@[simp] theorem dartWalk_edges (left right : I → V) (d : Dart I) :
    (dartWalk left right d).edges =
      [s(.inl (tail left right d), .inr d), s(.inr d, .inr (reverse d)),
        s(.inr (reverse d), .inl (head left right d))] := rfl

variable [Fintype I] [DecidableEq I] [DecidableEq V]

theorem next_tail_eq (left right : I → V) {d e : Dart I}
    (h : e ∈ successors left right d) : tail left right e = head left right d :=
  (Finset.mem_filter.mp (Finset.mem_erase.mp h).2).2

def subdividedWalk (left right : I → V) : (n : ℕ) → (p : Paths (Dart I) n) →
    Nonbacktracking left right n p →
    (edgeSubdivision left right).Walk (.inl (tail left right (first n p)))
      (.inl (head left right (last n p)))
  | 0, p, _ => dartWalk left right p
  | n + 1, p, hp =>
      (subdividedWalk left right n p.1 hp.1).append
        ((dartWalk left right p.2).copy (congrArg Sum.inl (next_tail_eq left right hp.2)) rfl)

end OnlineSteinerForest.UpperBound.Girth
