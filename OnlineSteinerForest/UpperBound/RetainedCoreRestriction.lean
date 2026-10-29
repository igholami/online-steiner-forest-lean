import OnlineSteinerForest.UpperBound.RetainedSparseCore

/-! Restrict actual request labels to the computed loopless core without changing their times. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical
variable {Z I T : Type*} [Fintype I] [DecidableEq Z] [DecidableEq I]

def coreLeft (left right : I → Z) (S : Finset Z)
    (i : ↥(liveEdges left right S)) : ↥S :=
  ⟨left i.val, (Finset.mem_filter.mp i.property).2.1⟩

def coreRight (left right : I → Z) (S : Finset Z)
    (i : ↥(liveEdges left right S)) : ↥S :=
  ⟨right i.val, (Finset.mem_filter.mp i.property).2.2.1⟩

def coreTime (left right : I → Z) (S : Finset Z) (time : I ↪ T) :
    ↥(liveEdges left right S) ↪ T :=
  (Function.Embedding.subtype _).trans time

theorem coreLeft_ne_coreRight (left right : I → Z) (S : Finset Z)
    (i : ↥(liveEdges left right S)) : coreLeft left right S i ≠ coreRight left right S i := by
  intro h
  exact (Finset.mem_filter.mp i.property).2.2.2 (congrArg Subtype.val h)

theorem core_label_count_le [Fintype T] (left right : I → Z) (S : Finset Z) (time : I ↪ T) :
    Fintype.card ↥(liveEdges left right S) ≤ Fintype.card T :=
  Fintype.card_le_of_embedding (coreTime left right S time)

end OnlineSteinerForest.UpperBound
