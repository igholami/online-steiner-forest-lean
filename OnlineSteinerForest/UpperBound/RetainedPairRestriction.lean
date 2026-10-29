import OnlineSteinerForest.UpperBound.SparseDiscard
import OnlineSteinerForest.UpperBound.RetainedZoneAssignment

/-! Restrict actual auxiliary labels and their copied endpoints to a small zone family. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

variable {Z I W : Type*} [DecidableEq Z] [DecidableEq I] [DecidableEq W]

noncomputable def restrictedAuxiliaryTime {n : ℕ} (time : I ↪ Fin n) (T : Finset I) : ↥T ↪ Fin n :=
  ⟨fun i => time i.val, fun a b h => Subtype.ext (time.injective h)⟩

noncomputable def restrictedZoneCopy (zones : Z → Finset (Sym2 W))
    (A : Finset Z) (T : Finset I) (zone : I → Z) (point : I → W)
    (hzone : ∀ i ∈ T, zone i ∈ A) (hsupport : ∀ i ∈ T, zoneSupport (zones (zone i)) (point i)) :
    ↥T → Σ z : ↥A, {w : W // zoneSupport (zones z.val) w} :=
  fun i => ⟨⟨zone i.val, hzone i.val i.property⟩, ⟨point i.val, hsupport i.val i.property⟩⟩

theorem restrictedZoneCopy_projects (zones : Z → Finset (Sym2 W))
    (A : Finset Z) (T : Finset I) (zone : I → Z) (point : I → W)
    (hzone : ∀ i ∈ T, zone i ∈ A) (hsupport : ∀ i ∈ T, zoneSupport (zones (zone i)) (point i))
    (i : ↥T) : (restrictedZoneCopy zones A T zone point hzone hsupport i).2.val = point i.val := rfl

variable [Fintype I]

/-- A proved cap for every subfamily on at most two zones supplies the exact
loop and parallel-edge hypotheses of the implemented peeling procedure. -/
theorem loops_parallel_caps_of_two_zone_caps (left right : I → Z) (S : Finset Z) (B : ℕ)
    (hcap : ∀ A : Finset Z, A ⊆ S → A.card ≤ 2 → ∀ T : Finset I,
      (∀ i ∈ T, left i ∈ A) → (∀ i ∈ T, right i ∈ A) → T.card ≤ B) :
    (∀ z ∈ S, (loopsAt left right z).card ≤ B) ∧
      ∀ u v, (parallelEdges left right S u v).card ≤ B := by
  constructor
  · intro z hz
    apply hcap {z} (Finset.singleton_subset_iff.mpr hz) (by simp)
    · intro i hi
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hi).2.1
    · intro i hi
      exact Finset.mem_singleton.mpr (Finset.mem_filter.mp hi).2.2
  · intro u v
    let A := ({u, v} : Finset Z) ∩ S
    have hcard : A.card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_left).trans
        ((Finset.card_insert_le _ _).trans (by simp))
    apply hcap A Finset.inter_subset_right hcard
    · intro i hi
      obtain ⟨hlive, hends⟩ := Finset.mem_filter.mp hi
      have hS := (Finset.mem_filter.mp hlive).2
      apply Finset.mem_inter.mpr
      refine ⟨?_, hS.1⟩
      rcases hends with ⟨hl, _⟩ | ⟨hl, _⟩ <;> simp [hl]
    · intro i hi
      obtain ⟨hlive, hends⟩ := Finset.mem_filter.mp hi
      have hS := (Finset.mem_filter.mp hlive).2
      apply Finset.mem_inter.mpr
      refine ⟨?_, hS.2.1⟩
      rcases hends with ⟨_, hr⟩ | ⟨_, hr⟩ <;> simp [hr]

end OnlineSteinerForest.UpperBound
