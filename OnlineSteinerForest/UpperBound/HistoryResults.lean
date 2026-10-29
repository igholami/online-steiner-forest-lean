import OnlineSteinerForest.UpperBound.MassEntropy
import OnlineSteinerForest.UpperBound.MassCharge
import OnlineSteinerForest.UpperBound.MassPaidLabels
import OnlineSteinerForest.UpperBound.AuxiliaryReferenceAccounting
import OnlineSteinerForest.UpperBound.OmissionsReferenceFamily
import OnlineSteinerForest.UpperBound.OmissionsOriginalFamily

/-! Component lifetimes, actual auxiliary extraction, dyadic batches, and their proved budgets.
The persistent analysis labels use union-by-positive-block-count; greedy itself is unchanged.
All mass, nearest-neighbor, endpoint, path-realization, and omission bounds are derived here. -/
