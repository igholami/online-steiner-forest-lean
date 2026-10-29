import OnlineSteinerForest.UpperBound.ZonesPartitionBoundary
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Restrict a connected zone to its actual support, then choose an actual spanning tree. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {W : Type*} [Fintype W] [DecidableEq W]

abbrev ZoneSupportVertex (F : Finset (Sym2 W)) := {v : W // zoneSupport F v}

def zoneSupportGraph (F : Finset (Sym2 W)) : SimpleGraph (ZoneSupportVertex F) :=
  (SimpleGraph.fromEdgeSet (F : Set (Sym2 W))).induce (zoneSupport F)

theorem zoneSupportGraph_connected (F : Finset (Sym2 W)) (hconn : ZoneConnected F)
    (hne : F.Nonempty) : (zoneSupportGraph F).Connected := by
  have hsupport : ∀ {u v : W} (p : (SimpleGraph.fromEdgeSet (F : Set (Sym2 W))).Walk u v),
      zoneSupport F u → ∀ w ∈ p.support, zoneSupport F w := by
    intro u v p
    induction p with
    | nil => intro hu w hw; simpa using (List.mem_singleton.mp hw ▸ hu)
    | @cons u v w huv p ih =>
      intro hu x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hu
      · exact ih ⟨s(u, v), huv.1, Sym2.mem_mk_right _ _⟩ x hx
  have hnonempty : Nonempty (ZoneSupportVertex F) := by
    obtain ⟨e, he⟩ := hne
    obtain ⟨v, hv⟩ : ∃ v, v ∈ e := Sym2.ind (fun a b => ⟨a, Sym2.mem_mk_left _ _⟩) e
    exact ⟨⟨v, e, he, hv⟩⟩
  letI := hnonempty
  refine ⟨?_⟩
  intro a b
  obtain ⟨e, he, hb⟩ := b.property
  obtain ⟨p⟩ := (hconn.root_at a.property) e he b.val hb
  exact ⟨p.induce (zoneSupport F) (hsupport p a.property)⟩

theorem exists_zone_copy_tree (F : Finset (Sym2 W)) (hconn : ZoneConnected F) (hne : F.Nonempty) :
    ∃ T : SimpleGraph (ZoneSupportVertex F), T ≤ zoneSupportGraph F ∧ T.IsTree := by
  obtain ⟨T, hT, hacyc, hreach⟩ := (zoneSupportGraph F).exists_isAcyclic_reachable_eq_le
  have hbase := zoneSupportGraph_connected F hconn hne
  refine ⟨T, hT, ⟨?_, hacyc⟩⟩
  letI := hbase.nonempty
  refine ⟨?_⟩
  intro u v
  rw [hreach]
  exact hbase u v

end OnlineSteinerForest.UpperBound
