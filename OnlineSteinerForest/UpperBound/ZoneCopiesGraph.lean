import OnlineSteinerForest.UpperBound.ThresholdFiberForest

/-! Disjoint copies of arbitrary zone trees form a standard simple forest. -/
namespace OnlineSteinerForest.UpperBound

variable {Z : Type*} {A : Z → Type*}

def zoneCopyGraph (T : ∀ z, SimpleGraph (A z)) : SimpleGraph (Σ z, A z) where
  Adj x y := ∃ z, ∃ u v : A z, (T z).Adj u v ∧ x = ⟨z, u⟩ ∧ y = ⟨z, v⟩
  symm.symm x y := by
    rintro ⟨z, u, v, huv, rfl, rfl⟩
    exact ⟨z, v, u, huv.symm, rfl, rfl⟩
  loopless.irrefl x := by
    rintro ⟨z, u, v, huv, rfl, heq⟩
    have huv' : u = v := by cases heq; rfl
    exact huv.ne huv'

theorem zoneCopyGraph_adj (T : ∀ z, SimpleGraph (A z)) (z : Z) (u v : A z) :
    (zoneCopyGraph T).Adj ⟨z, u⟩ ⟨z, v⟩ ↔ (T z).Adj u v := by
  constructor
  · rintro ⟨w, a, b, hab, hwu, hwv⟩
    have hw : w = z := (congrArg Sigma.fst hwu).symm
    subst w
    have hau : a = u := by cases hwu; rfl
    have hbv : b = v := by cases hwv; rfl
    simpa only [hau, hbv] using hab
  · intro huv
    exact ⟨z, u, v, huv, rfl, rfl⟩

def zoneCopyInclusion (T : ∀ z, SimpleGraph (A z)) (z : Z) : T z ↪g zoneCopyGraph T where
  toFun := Sigma.mk z
  inj' := by intro a b h; cases h; rfl
  map_rel_iff' := fun {u v} => zoneCopyGraph_adj T z u v

def zoneCopyFiber (T : ∀ z, SimpleGraph (A z)) (z : Z) :
    (zoneCopyGraph T).induce {v | v.1 = z} ↪g T z where
  toFun x := by
    rcases x with ⟨⟨w, a⟩, h⟩
    change w = z at h
    subst w
    exact a
  inj' := by
    rintro ⟨⟨w, a⟩, hw⟩ ⟨⟨v, b⟩, hv⟩ heq
    change w = z at hw
    change v = z at hv
    subst w
    subst v
    change a = b at heq
    subst b
    rfl
  map_rel_iff' := by
    rintro ⟨⟨w, a⟩, hw⟩ ⟨⟨v, b⟩, hv⟩
    change w = z at hw
    change v = z at hv
    subst w
    subst v
    exact (zoneCopyGraph_adj T z a b).symm

theorem zoneCopyGraph_acyclic (T : ∀ z, SimpleGraph (A z)) (hT : ∀ z, (T z).IsAcyclic) :
    (zoneCopyGraph T).IsAcyclic := by
  apply isAcyclic_of_fibers Sigma.fst
  · rintro x y ⟨z, u, v, huv, rfl, rfl⟩
    rfl
  · intro z
    exact (hT z).comap (zoneCopyFiber T z).toHom (zoneCopyFiber T z).injective

end OnlineSteinerForest.UpperBound
