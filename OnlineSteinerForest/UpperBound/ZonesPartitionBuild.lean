import OnlineSteinerForest.UpperBound.ZonesPartitionJoin
import OnlineSteinerForest.UpperBound.ZonesPartitionExtend
import OnlineSteinerForest.UpperBound.ZonesTreeRepresentation

/-! The manuscript's bottom-up construction on any ordinary finite bounded-edge tree. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def ZoneTree.partition {r : V} (t : ZoneTree V r) (ht : t.Valid)
    (G : SimpleGraph V) (hG : ∀ e ∈ t.edges, e ∈ G.edgeSet)
    (c : Sym2 V → ℝ) (M : ℝ) (hM : 0 < M) (hc : ∀ e ∈ t.edges, c e ≤ M) :
    ZonePartial r t.edges c M := by
  induction t with
  | leaf r => exact ZonePartial.empty r c M hM
  | extend r s t ih =>
    have hchild : ∀ e ∈ t.edges, e ∈ G.edgeSet := fun e he => hG e (Finset.mem_insert_of_mem he)
    have hcchild : ∀ e ∈ t.edges, c e ≤ M := fun e he => hc e (Finset.mem_insert_of_mem he)
    have hadj : G.Adj r s := hG s(r, s) (Finset.mem_insert_self _ _)
    exact (ih ht.2 hchild hcchild).extend hM hadj.ne ht.1 (hc _ (Finset.mem_insert_self _ _))
  | join r a b ha hb =>
    have hGa : ∀ e ∈ a.edges, e ∈ G.edgeSet := fun e he => hG e (Finset.mem_union_left _ he)
    have hGb : ∀ e ∈ b.edges, e ∈ G.edgeSet := fun e he => hG e (Finset.mem_union_right _ he)
    have hca : ∀ e ∈ a.edges, c e ≤ M := fun e he => hc e (Finset.mem_union_left _ he)
    have hcb : ∀ e ∈ b.edges, c e ≤ M := fun e he => hc e (Finset.mem_union_right _ he)
    exact (ha ht.2.1 hGa hca).join (hb ht.2.2 hGb hcb) hM ht.1

/-- The entire expression is connected at its root. -/
theorem ZoneTree.rooted {r : V} (t : ZoneTree V r) (hnd : ∀ e ∈ t.edges, ¬e.IsDiag) :
    ZoneRooted r t.edges := by
  induction t with
  | leaf r => exact ZoneRooted.empty r
  | extend r s t ih =>
    have hrs : r ≠ s := by simpa only [Sym2.mk_isDiag_iff] using hnd s(r, s) (Finset.mem_insert_self _ _)
    exact (ih (fun e he => hnd e (Finset.mem_insert_of_mem he))).extend hrs
  | join r a b ha hb =>
    exact (ha (fun e he => hnd e (Finset.mem_union_left _ he))).union
      (hb (fun e he => hnd e (Finset.mem_union_right _ he)))

/-- Every finite tree with edge weights at most `M` admits the required rooted
state; the sole leftover costs less than `M` and all emitted zones lie in `[M,2M)`. -/
theorem exists_zonePartial (G : SimpleGraph V) (hG : G.IsTree) (r : V)
    (c : Sym2 V → ℝ) (M : ℝ) (hM : 0 < M) (hc : ∀ e ∈ G.edgeSet, c e ≤ M) :
    Nonempty (ZonePartial r G.edgeFinset c M) := by
  obtain ⟨t, ht, he, _⟩ := exists_zoneTree G hG r
  have hmem : ∀ e ∈ t.edges, e ∈ G.edgeSet := by
    intro e h
    exact G.mem_edgeFinset.mp (he ▸ h)
  have hs : ∀ e ∈ t.edges, c e ≤ M := fun e h => hc e (hmem e h)
  exact ⟨he ▸ t.partition ht G hmem c M hM hs⟩

end OnlineSteinerForest.UpperBound
