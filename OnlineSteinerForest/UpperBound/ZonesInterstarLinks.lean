import OnlineSteinerForest.UpperBound.ZonesInterstarForest

/-! Assignment and interstar edges are actual selected core-graph links. -/
namespace OnlineSteinerForest.UpperBound.InterstarForest

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {centers : Finset V} {stars : StarContraction G centers}

def Link (f : InterstarForest stars) := {v : V // v ∉ centers} ⊕ ↥f.graph.edgeFinset

noncomputable instance (f : InterstarForest stars) : Fintype f.Link := by
  unfold Link
  infer_instance

def linkLeft (f : InterstarForest stars) : f.Link → V
  | .inl v => v.val
  | .inr e => f.left e

def linkRight (f : InterstarForest stars) : f.Link → V
  | .inl v => (stars.assign v.val).val
  | .inr e => f.right e

theorem link_adjacent (f : InterstarForest stars) (i : f.Link) :
    G.Adj (f.linkLeft i) (f.linkRight i) := by
  cases i with
  | inl v => exact stars.adjacent v.val v.property
  | inr e => exact f.adjacent e

theorem link_count_le (f : InterstarForest stars) : Fintype.card f.Link ≤ Fintype.card V := by
  have he := f.edge_count_le
  have hc := Finset.card_le_univ centers
  simp only [Link, Fintype.card_sum, Fintype.card_subtype_compl, Fintype.card_coe]
  omega

end OnlineSteinerForest.UpperBound.InterstarForest
