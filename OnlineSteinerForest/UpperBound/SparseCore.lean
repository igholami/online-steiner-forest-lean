import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-! Deterministic peeling of a finite zone multigraph, with labelled auxiliary edges.
Only its endpoints are needed; loops are removed before degree peeling. -/
namespace OnlineSteinerForest.UpperBound

variable {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]

def liveEdges (left right : I → V) (S : Finset V) : Finset I :=
  Finset.univ.filter (fun i => left i ∈ S ∧ right i ∈ S ∧ left i ≠ right i)

def incidentEdges (left right : I → V) (S : Finset V) (v : V) : Finset I :=
  (liveEdges left right S).filter (fun i => left i = v ∨ right i = v)

/-- Repeatedly remove any vertex below the required degree. -/
noncomputable def sparseCore (left right : I → V) (D : ℕ) (S : Finset V) : Finset V :=
  if h : ∃ v ∈ S, (incidentEdges left right S v).card < D then
    sparseCore left right D (S.erase (Classical.choose h))
  else S
termination_by S.card
decreasing_by exact Finset.card_erase_lt_of_mem (Classical.choose_spec h).1

end OnlineSteinerForest.UpperBound
