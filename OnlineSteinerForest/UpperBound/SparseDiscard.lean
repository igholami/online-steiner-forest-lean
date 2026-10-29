import OnlineSteinerForest.UpperBound.SparsePeeling
import OnlineSteinerForest.UpperBound.SparseDegree

/-! Account for loops and peeled edges in the actual finite zone-core algorithm. -/
namespace OnlineSteinerForest.UpperBound

variable {V I : Type*} [Fintype I] [DecidableEq V] [DecidableEq I]

def loopEdges (left right : I → V) (S : Finset V) : Finset I :=
  Finset.univ.filter (fun i => left i ∈ S ∧ left i = right i)

def loopsAt (left right : I → V) (v : V) : Finset I :=
  Finset.univ.filter (fun i => left i = v ∧ right i = v)

omit [DecidableEq I] in
theorem loop_card_le (left right : I → V) (S : Finset V) (B : ℕ)
    (hcap : ∀ v ∈ S, (loopsAt left right v).card ≤ B) :
    (loopEdges left right S).card ≤ B * S.card := by
  have hf : ∀ v ∈ (loopEdges left right S).image left,
      ((loopEdges left right S).filter (fun i => left i = v)).card ≤ B := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    have hiS := (Finset.mem_filter.mp hi).2.1
    apply (Finset.card_le_card (show
      (loopEdges left right S).filter (fun j => left j = left i) ⊆ loopsAt left right (left i) from ?_)).trans
      (hcap (left i) hiS)
    intro j hj
    obtain ⟨hj, hji⟩ := Finset.mem_filter.mp hj
    have he := (Finset.mem_filter.mp hj).2.2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hji, he.symm.trans hji⟩
  have hc := Finset.card_le_mul_card_image (f := left) (loopEdges left right S) B hf
  have hsub : (loopEdges left right S).image left ⊆ S := by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2.1
  exact hc.trans (Nat.mul_le_mul_left B (Finset.card_le_card hsub))

theorem card_edges_partition (left right : I → V) (S : Finset V)
    (hleft : ∀ i, left i ∈ S) (hright : ∀ i, right i ∈ S) :
    Fintype.card I = (liveEdges left right S).card + (loopEdges left right S).card := by
  have hdis : Disjoint (liveEdges left right S) (loopEdges left right S) := by
    apply Finset.disjoint_left.mpr
    intro i hi hl
    exact (Finset.mem_filter.mp hi).2.2.2 ((Finset.mem_filter.mp hl).2.2)
  have heq : liveEdges left right S ∪ loopEdges left right S = Finset.univ := by
    ext i
    simp only [liveEdges, loopEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases hi : left i = right i
    · exact Or.inr ⟨hleft i, hi⟩
    · exact Or.inl ⟨hleft i, hright i, hi⟩
  rw [← Finset.card_univ (α := I), ← heq, Finset.card_union_of_disjoint hdis]

/-- At most `(loop cap + peeling threshold)` edges are charged to each original zone. -/
theorem discarded_edges_le (left right : I → V) (S : Finset V) (B D : ℕ)
    (hleft : ∀ i, left i ∈ S) (hright : ∀ i, right i ∈ S)
    (hloops : ∀ v ∈ S, (loopsAt left right v).card ≤ B) :
    Fintype.card I - (liveEdges left right (sparseCore left right D S)).card ≤ (B + D) * S.card := by
  have hpartition := card_edges_partition left right S hleft hright
  have hloop := loop_card_le left right S B hloops
  have hbudget := (sparseCore_spec left right D S).2.2
  have hmul := Nat.mul_le_mul_left D (Nat.sub_le S.card (sparseCore left right D S).card)
  rw [Nat.add_mul]
  omega

end OnlineSteinerForest.UpperBound
