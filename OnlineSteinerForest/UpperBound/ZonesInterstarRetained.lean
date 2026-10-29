import OnlineSteinerForest.UpperBound.ZonesInterstarLinks

/-! Full zone trees are retained only at centers and interstar endpoints. -/
namespace OnlineSteinerForest.UpperBound.InterstarForest

open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
  {centers : Finset V} {stars : StarContraction G centers}

noncomputable def retainedZones (f : InterstarForest stars) : Finset V :=
  centers ∪ Finset.univ.image f.left ∪ Finset.univ.image f.right

theorem center_retained (f : InterstarForest stars) {v : V} (hv : v ∈ centers) :
    v ∈ f.retainedZones := Finset.mem_union_left _ (Finset.mem_union_left _ hv)

theorem left_retained (f : InterstarForest stars) (i : ↥f.graph.edgeFinset) :
    f.left i ∈ f.retainedZones :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

theorem right_retained (f : InterstarForest stars) (i : ↥f.graph.edgeFinset) :
    f.right i ∈ f.retainedZones :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))

theorem retained_count_le (f : InterstarForest stars) : f.retainedZones.card ≤ 3 * centers.card := by
  have hleft : (Finset.univ.image f.left).card ≤ f.graph.edgeFinset.card := by
    exact Finset.card_image_le.trans_eq (by simp)
  have hright : (Finset.univ.image f.right).card ≤ f.graph.edgeFinset.card := by
    exact Finset.card_image_le.trans_eq (by simp)
  have hfirst := Finset.card_union_le centers (Finset.univ.image f.left)
  have hsecond := Finset.card_union_le (centers ∪ Finset.univ.image f.left)
    (Finset.univ.image f.right)
  have he := f.edge_count_le
  change (centers ∪ Finset.univ.image f.left ∪ Finset.univ.image f.right).card ≤ _
  omega

end OnlineSteinerForest.UpperBound.InterstarForest
