import OnlineSteinerForest.Graph.Paths

/-! Auxiliary output data contains original vertices and an original-edge realizing path. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

structure AuxiliaryOutput (V : Type*) where
  left : V
  right : V
  edges : Finset (Sym2 V)

end OnlineSteinerForest.UpperBound
