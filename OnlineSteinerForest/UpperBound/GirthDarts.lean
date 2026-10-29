import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Bool.Basic

/-! Oriented edges and nonbacktracking successors for a finite labelled multigraph.
A loop has two orientations, so it contributes two to its vertex degree. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]

abbrev Dart (I : Type*) := I × Bool

def reverse (d : Dart I) : Dart I := (d.1, !d.2)

def tail (left right : I → V) (d : Dart I) : V := if d.2 then right d.1 else left d.1

def head (left right : I → V) (d : Dart I) : V := if d.2 then left d.1 else right d.1

omit [Fintype I] [DecidableEq I] in
@[simp] theorem reverse_reverse (d : Dart I) : reverse (reverse d) = d := by
  rcases d with ⟨i, b⟩
  cases b <;> rfl

theorem reverse_injective : Function.Injective (@reverse I) :=
  Function.Involutive.injective reverse_reverse

omit [Fintype I] [DecidableEq I] [DecidableEq V] in
@[simp] theorem tail_reverse (left right : I → V) (d : Dart I) :
    tail left right (reverse d) = head left right d := by rcases d with ⟨i, b⟩; cases b <;> rfl

omit [Fintype I] [DecidableEq I] [DecidableEq V] in
@[simp] theorem head_reverse (left right : I → V) (d : Dart I) :
    head left right (reverse d) = tail left right d := by rcases d with ⟨i, b⟩; cases b <;> rfl

def outgoing (left right : I → V) (v : V) : Finset (Dart I) :=
  Finset.univ.filter (fun d => tail left right d = v)

def incoming (left right : I → V) (v : V) : Finset (Dart I) :=
  Finset.univ.filter (fun d => head left right d = v)

def degree (left right : I → V) (v : V) : ℕ := (outgoing left right v).card

def successors (left right : I → V) (d : Dart I) : Finset (Dart I) :=
  (outgoing left right (head left right d)).erase (reverse d)

def predecessors (left right : I → V) (d : Dart I) : Finset (Dart I) :=
  (incoming left right (tail left right d)).erase (reverse d)

theorem incoming_eq_image_reverse (left right : I → V) (v : V) :
    incoming left right v = (outgoing left right v).image reverse := by
  ext d
  constructor
  · intro hd
    refine Finset.mem_image.mpr ⟨reverse d, ?_, reverse_reverse d⟩
    simpa only [outgoing, incoming, Finset.mem_filter, Finset.mem_univ, true_and, tail_reverse] using hd
  · intro hd
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd
    simpa only [incoming, outgoing, Finset.mem_filter, Finset.mem_univ, true_and, head_reverse] using he

theorem incoming_card (left right : I → V) (v : V) :
    (incoming left right v).card = degree left right v := by
  rw [incoming_eq_image_reverse, Finset.card_image_of_injective _ reverse_injective]
  rfl

theorem successors_card (left right : I → V) (d : Dart I) :
    (successors left right d).card = degree left right (head left right d) - 1 := by
  unfold successors
  rw [Finset.card_erase_of_mem (by simp [outgoing])]
  rfl

theorem predecessors_card (left right : I → V) (d : Dart I) :
    (predecessors left right d).card = degree left right (tail left right d) - 1 := by
  unfold predecessors
  rw [Finset.card_erase_of_mem (by simp [incoming]), incoming_card]

theorem mem_successors_iff_mem_predecessors (left right : I → V) (d e : Dart I) :
    e ∈ successors left right d ↔ d ∈ predecessors left right e := by
  have hne : e ≠ reverse d ↔ d ≠ reverse e := by
    constructor
    · intro h heq
      exact h (by simpa only [reverse_reverse] using (congrArg reverse heq).symm)
    · intro h heq
      exact h (by simpa only [reverse_reverse] using (congrArg reverse heq).symm)
  simp only [successors, predecessors, outgoing, incoming, Finset.mem_erase, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact and_congr hne eq_comm

end OnlineSteinerForest.UpperBound.Girth
