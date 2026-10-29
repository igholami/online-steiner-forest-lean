import OnlineSteinerForest.Graph.Feasibility

/-! Connectivity on the support of an edge set, including an empty root leftover. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V]

/-- Every endpoint of every retained edge is reachable from the specified root. -/
def ZoneRooted (r : V) (F : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ F, ∀ v ∈ e, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable r v

/-- A zone is connected on its actual edge support. -/
def ZoneConnected (F : Finset (Sym2 V)) : Prop := ∃ r, ZoneRooted r F

theorem fromEdges_mono {F H : Finset (Sym2 V)} (h : F ⊆ H) :
    SimpleGraph.fromEdgeSet (F : Set (Sym2 V)) ≤ SimpleGraph.fromEdgeSet (H : Set (Sym2 V)) := by
  intro u v huv
  exact ⟨h huv.1, huv.2⟩

theorem ZoneRooted.empty (r : V) : ZoneRooted r ∅ := by simp [ZoneRooted]

theorem ZoneRooted.union {r : V} {F H : Finset (Sym2 V)}
    (hF : ZoneRooted r F) (hH : ZoneRooted r H) : ZoneRooted r (F ∪ H) := by
  intro e he v hv
  rcases Finset.mem_union.mp he with he | he
  · exact (hF e he v hv).mono (fromEdges_mono Finset.subset_union_left)
  · exact (hH e he v hv).mono (fromEdges_mono Finset.subset_union_right)

theorem ZoneRooted.extend {r s : V} {F : Finset (Sym2 V)} (hF : ZoneRooted s F)
    (hrs : r ≠ s) : ZoneRooted r (insert s(r, s) F) := by
  have hadj : (SimpleGraph.fromEdgeSet ((insert s(r, s) F : Finset (Sym2 V)) : Set (Sym2 V))).Adj r s :=
    ⟨Finset.mem_insert_self _ _, hrs⟩
  intro e he v hv
  rcases Finset.mem_insert.mp he with rfl | he
  · rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact SimpleGraph.Reachable.refl _
    · exact hadj.reachable
  · exact hadj.reachable.trans ((hF e he v hv).mono (fromEdges_mono (Finset.subset_insert _ _)))

theorem ZoneRooted.connected {r : V} {F : Finset (Sym2 V)} (hF : ZoneRooted r F) :
    ZoneConnected F := ⟨r, hF⟩

end OnlineSteinerForest.UpperBound
