import OnlineSteinerForest.UpperBound.ZonesPartitionFamily
import OnlineSteinerForest.UpperBound.AuxiliaryHelpful

/-! Assign each actual auxiliary endpoint to a containing reference zone. -/
namespace OnlineSteinerForest.UpperBound

universe uSelection
variable [OnlineSteinerForest.PathSelection.{uSelection}]

open scoped Classical
variable {V W : Type uSelection} {I : Type*} [DecidableEq W]

noncomputable def assignedZone (zones : Finset (Finset (Sym2 W))) (v : W)
    (h : ∃ Z ∈ zones, zoneSupport Z v) : ↥zones :=
  ⟨h.choose, h.choose_spec.1⟩

theorem assignedZone_support (zones : Finset (Finset (Sym2 W))) (v : W)
    (h : ∃ Z ∈ zones, zoneSupport Z v) :
    zoneSupport (assignedZone zones v h).val v := h.choose_spec.2

noncomputable def assignedCopy (zones : Finset (Finset (Sym2 W))) (v : W)
    (h : ∃ Z ∈ zones, zoneSupport Z v) :
    Σ Z : ↥zones, {w : W // zoneSupport Z.val w} :=
  ⟨assignedZone zones v h, ⟨v, assignedZone_support zones v h⟩⟩

theorem assignedCopy_projects (zones : Finset (Finset (Sym2 W))) (v : W)
    (h : ∃ Z ∈ zones, zoneSupport Z v) : (assignedCopy zones v h).2.val = v := rfl

end OnlineSteinerForest.UpperBound
