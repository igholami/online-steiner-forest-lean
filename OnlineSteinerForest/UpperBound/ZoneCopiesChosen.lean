import OnlineSteinerForest.UpperBound.ZoneCopiesReference
import OnlineSteinerForest.UpperBound.ZoneCopiesComponents

/-! Canonical classical choices of actual spanning trees inside connected zones. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]
open scoped Classical
variable {Z W : Type*} [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
noncomputable def chosenZoneTrees (zones : Z → Finset (Sym2 W))
    (hconn : ∀ z, ZoneConnected (zones z)) (hne : ∀ z, (zones z).Nonempty) :
    ∀ z, SimpleGraph (ZoneSupportVertex (zones z)) :=
  fun z => Classical.choose (exists_zone_copy_tree (zones z) (hconn z) (hne z))
theorem chosenZoneTrees_le (zones : Z → Finset (Sym2 W))
    (hconn : ∀ z, ZoneConnected (zones z)) (hne : ∀ z, (zones z).Nonempty) (z : Z) :
    chosenZoneTrees zones hconn hne z ≤ zoneSupportGraph (zones z) :=
  (Classical.choose_spec (exists_zone_copy_tree (zones z) (hconn z) (hne z))).1
theorem chosenZoneTrees_tree (zones : Z → Finset (Sym2 W))
    (hconn : ∀ z, ZoneConnected (zones z)) (hne : ∀ z, (zones z).Nonempty) (z : Z) :
    (chosenZoneTrees zones hconn hne z).IsTree :=
  (Classical.choose_spec (exists_zone_copy_tree (zones z) (hconn z) (hne z))).2
end OnlineSteinerForest.UpperBound
