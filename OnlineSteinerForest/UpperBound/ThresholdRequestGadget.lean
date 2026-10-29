import OnlineSteinerForest.UpperBound.ChargingGraph
import OnlineSteinerForest.UpperBound.ChargingReference

/-! Request indices give chronological labels and an original-vertex projection for the charging graph. -/
namespace OnlineSteinerForest.UpperBound

variable {V J : Type*} [DecidableEq V]

def requestLeft (requests : List (V × V)) (index : J → Fin requests.length) (j : J) : V :=
  requests[(index j).val].1

def requestRight (requests : List (V × V)) (index : J → Fin requests.length) (j : J) : V :=
  requests[(index j).val].2

def requestProjection (requests : List (V × V)) (index : J → Fin requests.length) : (V ⊕ J) → V
  | .inl v => v
  | .inr j => requestLeft requests index j

noncomputable def requestLabel (requests : List (V × V)) (index : J → Fin requests.length)
    (e : Sym2 (V ⊕ J)) : Option ℕ :=
  (Charging.edgeLabel (requestRight requests index) e).map (fun j => (index j).val)

theorem edgeLabel_eq_middle (right : J → V) (e : Sym2 (V ⊕ J)) (j : J)
    (hl : Charging.edgeLabel right e = some j) : e = Charging.middle right j := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    cases a with
    | inl u =>
      cases b with
      | inl v => simp [Charging.edgeLabel] at hl
      | inr k =>
        by_cases hu : u = right k
        · have hk : k = j := by simpa [Charging.edgeLabel, hu] using hl
          subst j
          subst u
          exact Sym2.eq_swap
        · simp [Charging.edgeLabel, hu] at hl
    | inr k =>
      cases b with
      | inl u =>
        by_cases hu : u = right k
        · have hk : k = j := by simpa [Charging.edgeLabel, hu] using hl
          subst j
          subst u
          rfl
        · simp [Charging.edgeLabel, hu] at hl
      | inr l => simp [Charging.edgeLabel] at hl

theorem requestLabel_unique (requests : List (V × V)) (index : J → Fin requests.length)
    (hinj : Function.Injective index) (e f : Sym2 (V ⊕ J)) (i : ℕ)
    (he : requestLabel requests index e = some i) (hf : requestLabel requests index f = some i) : e = f := by
  obtain ⟨j, hj, hji⟩ := Option.map_eq_some_iff.mp he
  obtain ⟨k, hk, hki⟩ := Option.map_eq_some_iff.mp hf
  have hjk : j = k := hinj (Fin.ext (hji.trans hki.symm))
  exact (edgeLabel_eq_middle _ e j hj).trans ((hjk ▸ edgeLabel_eq_middle _ f k hk).symm)

theorem requestLabel_reference_forest (H : SimpleGraph V) (hH : H.IsAcyclic)
    (requests : List (V × V)) (index : J → Fin requests.length)
    (hne : ∀ j, requestLeft requests index j ≠ requestRight requests index j) :
    ((Charging.graph H (requestLeft requests index) (requestRight requests index)).deleteEdges
      {e | requestLabel requests index e ≠ none}).IsAcyclic := by
  have heq : {e | requestLabel requests index e ≠ none} =
      {e | Charging.edgeLabel (requestRight requests index) e ≠ none} := by
    ext e
    simp [requestLabel]
  rw [heq, Charging.reference_delete_eq H _ _ hne]
  exact Charging.referenceSpokes_acyclic H hH _

end OnlineSteinerForest.UpperBound
