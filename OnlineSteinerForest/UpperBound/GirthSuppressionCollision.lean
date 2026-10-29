import OnlineSteinerForest.UpperBound.GirthCollision
import OnlineSteinerForest.UpperBound.GirthExpandValid
import OnlineSteinerForest.UpperBound.GirthExpandInjective
import OnlineSteinerForest.UpperBound.GirthExpandChain

/-! Full collision-witness lifting through actual degree-two suppression. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq I] [DecidableEq V]

def expandCollision (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (p : Collision (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels)) : Collision left right where
  start := p.start.val
  finish := p.finish.val
  firstTrace := expandTrace d e p.firstTrace
  secondTrace := expandTrace d e p.secondTrace
  firstValid := expandTrace_valid left right v d e hpair hlabels p.firstTrace p.firstValid
  secondValid := expandTrace_valid left right v d e hpair hlabels p.secondTrace p.secondValid
  firstNonbacktracking := expandTrace_chain d e hlabels p.firstTrace p.firstNonbacktracking
  secondNonbacktracking := expandTrace_chain d e hlabels p.secondTrace p.secondNonbacktracking
  distinct := fun h => p.distinct (expandTrace_injective d e hlabels h)

theorem expandCollision_cost (left right : I → V) (v : V) (d e : Dart I)
    (hpair : outgoing left right v = {d, e}) (hlabels : d.1 ≠ e.1)
    (p : Collision (suppressedLeft left right v d e hpair hlabels)
      (suppressedRight left right v d e hpair hlabels)) (w : I → ℝ) :
    (expandCollision left right v d e hpair hlabels p).cost w = p.cost (suppressedWeight w d e) := by
  simp only [Collision.cost, expandCollision, expandTrace_cost]

end OnlineSteinerForest.UpperBound.Girth
