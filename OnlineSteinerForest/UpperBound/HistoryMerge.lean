import OnlineSteinerForest.Graph.Cost

/-! Union-by-size bookkeeping for persistent labels.
This changes only the analysis labels, not the greedy edge-purchase algorithm.
Members are positive-payment request blocks; the largest touched block set keeps its label. -/
namespace OnlineSteinerForest.UpperBound

structure LabeledCluster (ι : Type*) where
  label : ι
  members : Finset ι
  deriving DecidableEq

structure MergeHistory (ι : Type*) where
  active : Finset (LabeledCluster ι)
  retired : List (LabeledCluster ι)

namespace MergeHistory

variable {ι : Type*} [DecidableEq ι]

def empty : MergeHistory ι := ⟨∅, []⟩

noncomputable def chosen (touched : Finset (LabeledCluster ι)) (ht : touched.Nonempty) : LabeledCluster ι :=
  Classical.choose (touched.exists_max_image (fun C => C.members.card) ht)

omit [DecidableEq ι] in
theorem chosen_mem (touched : Finset (LabeledCluster ι)) (ht : touched.Nonempty) :
    chosen touched ht ∈ touched := (Classical.choose_spec
      (touched.exists_max_image (fun C => C.members.card) ht)).1

omit [DecidableEq ι] in
theorem chosen_max (touched : Finset (LabeledCluster ι)) (ht : touched.Nonempty)
    (C : LabeledCluster ι) (hC : C ∈ touched) : C.members.card ≤ (chosen touched ht).members.card :=
  (Classical.choose_spec (touched.exists_max_image (fun C => C.members.card) ht)).2 C hC

noncomputable def winner (new : ι) (touched : Finset (LabeledCluster ι)) : ι :=
  if ht : touched.Nonempty then (chosen touched ht).label else new

noncomputable def merged (new : ι) (touched : Finset (LabeledCluster ι)) : LabeledCluster ι :=
  ⟨winner new touched, insert new (touched.biUnion LabeledCluster.members)⟩

noncomputable def losers (new : ι) (touched : Finset (LabeledCluster ι)) : Finset (LabeledCluster ι) := by
  classical
  exact touched.filter (fun C => C.label ≠ winner new touched)

/-- Retire all touched labels except the maximum-size survivor, and install their merged component. -/
noncomputable def step (state : MergeHistory ι) (new : ι)
    (touched : Finset (LabeledCluster ι)) : MergeHistory ι :=
  ⟨insert (merged new touched) (state.active \ touched), (losers new touched).toList ++ state.retired⟩

@[simp] theorem new_mem_merged (new : ι) (touched : Finset (LabeledCluster ι)) :
    new ∈ (merged new touched).members := Finset.mem_insert_self _ _

theorem touched_subset_merged (new : ι) (touched : Finset (LabeledCluster ι))
    (C : LabeledCluster ι) (hC : C ∈ touched) : C.members ⊆ (merged new touched).members := by
  intro a ha
  exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨C, hC, ha⟩)

theorem merged_mem_step (state : MergeHistory ι) (new : ι) (touched : Finset (LabeledCluster ι)) :
    merged new touched ∈ (step state new touched).active := Finset.mem_insert_self _ _

theorem untouched_mem_step (state : MergeHistory ι) (new : ι) (touched : Finset (LabeledCluster ι))
    (C : LabeledCluster ι) (hC : C ∈ state.active) (hCt : C ∉ touched) :
    C ∈ (step state new touched).active := Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hC, hCt⟩)

theorem winner_label_of_nonempty (new : ι) (touched : Finset (LabeledCluster ι)) (ht : touched.Nonempty) :
    (merged new touched).label = (chosen touched ht).label := by simp [merged, winner, ht]

end MergeHistory
end OnlineSteinerForest.UpperBound
