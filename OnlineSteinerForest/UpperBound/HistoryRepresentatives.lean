import OnlineSteinerForest.UpperBound.HistoryGreedy
import OnlineSteinerForest.UpperBound.HistoryRelations
import Mathlib.Data.List.GetD

/-! Live labels genuinely group requests from one actual bought component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def requestSource (requests : List (V × V)) (fallback : V) (i : ℕ) : V :=
  (requests.getD i (fallback, fallback)).1

@[simp] theorem requestSource_eq (requests : List (V × V)) (fallback : V)
    (i : ℕ) (hi : i < requests.length) : requestSource requests fallback i = requests[i].1 := by
  simp only [requestSource, List.getD_eq_getElem requests (fallback, fallback) hi]

theorem greedyHistory_members_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (fallback : V) (i : ℕ) (C : LabeledCluster ℕ)
    (hC : C ∈ (greedyHistory G c requests feasible i).active)
    (a : ℕ) (ha : a ∈ C.members) (b : ℕ) (hb : b ∈ C.members) :
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).Reachable
      (requestSource requests fallback a) (requestSource requests fallback b) := by
  apply scanHistory_members_related
    (fun j => 0 < blockPayment G c requests feasible j) (touchesBlock G c requests feasible)
    (fun j a b => (SimpleGraph.fromEdgeSet
      (boughtBefore G c requests feasible j : Set (Sym2 V))).Reachable
        (requestSource requests fallback a) (requestSource requests fallback b)) _ _ _ i C hC a ha b hb
  · intro j
    exact ⟨fun a => .refl _, fun h => h.symm, fun h h' => h.trans h'⟩
  · intro j a b h
    exact reachable_mono_edges (boughtBefore_mono G c requests feasible j (j + 1) (by omega)) h
  · intro j D hD
    obtain ⟨hj, hDl, hreach⟩ := hD
    simpa only [requestSource_eq requests fallback j hj,
      requestSource_eq requests fallback D.label hDl] using hreach

end OnlineSteinerForest.UpperBound
