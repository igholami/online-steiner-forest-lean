import OnlineSteinerForest.UpperBound.ZonesPartitionConnected
import Mathlib.Tactic.Linarith

/-! Bottom-up zone states keep a small connected leftover at the current root. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [DecidableEq V]

def zoneUnion (Z : List (Finset (Sym2 V))) : Finset (Sym2 V) := Z.foldr (· ∪ ·) ∅

@[simp] theorem zoneUnion_nil : zoneUnion ([] : List (Finset (Sym2 V))) = ∅ := rfl
@[simp] theorem zoneUnion_cons (F : Finset (Sym2 V)) (Z : List (Finset (Sym2 V))) :
    zoneUnion (F :: Z) = F ∪ zoneUnion Z := rfl
@[simp] theorem zoneUnion_append (Z T : List (Finset (Sym2 V))) :
    zoneUnion (Z ++ T) = zoneUnion Z ∪ zoneUnion T := by
  induction Z with
  | nil => simp
  | cons F Z ih => simp [ih, Finset.union_assoc]

@[simp] theorem mem_zoneUnion (e : Sym2 V) (Z : List (Finset (Sym2 V))) :
    e ∈ zoneUnion Z ↔ ∃ F ∈ Z, e ∈ F := by
  induction Z with
  | nil => simp
  | cons F Z ih => simp [ih, or_and_right, exists_or]

structure ZonePartial (r : V) (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (M : ℝ) where
  zones : List (Finset (Sym2 V))
  leftover : Finset (Sym2 V)
  covers : zoneUnion zones ∪ leftover = E
  disjoint : (leftover :: zones).Pairwise Disjoint
  rooted : ZoneRooted r leftover
  small : edgeCost c leftover < M
  good : ∀ F ∈ zones, ZoneConnected F ∧ M ≤ edgeCost c F ∧ edgeCost c F < 2 * M

namespace ZonePartial
variable {r : V} {E : Finset (Sym2 V)} {c : Sym2 V → ℝ} {M : ℝ}

theorem leftover_subset (p : ZonePartial r E c M) : p.leftover ⊆ E := by
  intro e he
  exact p.covers ▸ Finset.mem_union_right (zoneUnion p.zones) he

theorem zone_subset (p : ZonePartial r E c M) {F : Finset (Sym2 V)} (hF : F ∈ p.zones) : F ⊆ E := by
  intro e he
  rw [← p.covers]
  exact Finset.mem_union_left _ ((mem_zoneUnion e p.zones).mpr ⟨F, hF, he⟩)

theorem left_disjoint (p : ZonePartial r E c M) {F : Finset (Sym2 V)} (hF : F ∈ p.zones) :
    Disjoint p.leftover F := (List.pairwise_cons.mp p.disjoint).1 F hF

/-- Output a leftover once it reaches the target, keeping an empty root leftover. -/
noncomputable def close (r : V) (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (M : ℝ)
    (hM : 0 < M) (Z : List (Finset (Sym2 V))) (L : Finset (Sym2 V))
    (hcover : zoneUnion Z ∪ L = E) (hdisj : (L :: Z).Pairwise Disjoint)
    (hroot : ZoneRooted r L) (hcost : edgeCost c L < 2 * M)
    (hgood : ∀ F ∈ Z, ZoneConnected F ∧ M ≤ edgeCost c F ∧ edgeCost c F < 2 * M) :
    ZonePartial r E c M := by
  by_cases hlarge : M ≤ edgeCost c L
  · refine ⟨L :: Z, ∅, ?_, ?_, ZoneRooted.empty r, ?_, ?_⟩
    · simpa [Finset.union_comm] using hcover
    · rw [List.pairwise_cons]
      exact ⟨fun _ _ => by simp, hdisj⟩
    · simpa [edgeCost] using hM
    · intro F hF
      rcases List.mem_cons.mp hF with rfl | hF
      · exact ⟨hroot.connected, hlarge, hcost⟩
      · exact hgood F hF
  · exact ⟨Z, L, hcover, hdisj, hroot, lt_of_not_ge hlarge, hgood⟩

noncomputable def empty (r : V) (c : Sym2 V → ℝ) (M : ℝ) (hM : 0 < M) :
    ZonePartial r ∅ c M :=
  ⟨[], ∅, by simp, by simp, ZoneRooted.empty r, by simpa [edgeCost] using hM, by simp⟩

end ZonePartial
end OnlineSteinerForest.UpperBound
