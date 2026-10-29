import OnlineSteinerForest.UpperBound.ZonesSubdivisionWalk
import OnlineSteinerForest.UpperBound.ZonesSubdivisionRecombine

/-! Composable subdivision certificates track original marked vertices and whole-edge recovery. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
universe u v w

structure ZoneSubdivisionCertificate {V : Type u} {W : Type v}
    (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) (F : Finset (Sym2 W)) (d : Sym2 W → ℝ) where
  vertices : V ↪ W
  cost_eq : edgeCost d F = edgeCost c E
  realize : ∀ {a b : V} (p : (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))).Walk a b),
    ∃ q : (SimpleGraph.fromEdgeSet (F : Set (Sym2 W))).Walk (vertices a) (vertices b),
      walkCost d q = walkCost c p
  recover : ∀ H : Finset (Sym2 W), H ⊆ F → ∃ P : Finset (Sym2 V), P ⊆ E ∧
    edgeCost c P ≤ edgeCost d H ∧ ∀ a b : V,
      (SimpleGraph.fromEdgeSet (H : Set (Sym2 W))).Reachable (vertices a) (vertices b) →
      (SimpleGraph.fromEdgeSet (P : Set (Sym2 V))).Reachable a b

namespace ZoneSubdivisionCertificate
variable {V : Type u} {W : Type v} {X : Type w}

noncomputable def refl (E : Finset (Sym2 V)) (c : Sym2 V → ℝ) : ZoneSubdivisionCertificate E c E c where
  vertices := Function.Embedding.refl _
  cost_eq := rfl
  realize p := ⟨p, rfl⟩
  recover H hH := ⟨H, hH, le_rfl, fun _ _ h => h⟩

noncomputable def trans {E : Finset (Sym2 V)} {c : Sym2 V → ℝ}
    {F : Finset (Sym2 W)} {d : Sym2 W → ℝ} {J : Finset (Sym2 X)} {k : Sym2 X → ℝ}
    (a : ZoneSubdivisionCertificate E c F d) (b : ZoneSubdivisionCertificate F d J k) :
    ZoneSubdivisionCertificate E c J k where
  vertices := a.vertices.trans b.vertices
  cost_eq := b.cost_eq.trans a.cost_eq
  realize p := by
    obtain ⟨q, hq⟩ := a.realize p
    obtain ⟨t, ht⟩ := b.realize q
    exact ⟨t, ht.trans hq⟩
  recover H hH := by
    obtain ⟨P, hP, hcostP, hreachP⟩ := b.recover H hH
    obtain ⟨Q, hQ, hcostQ, hreachQ⟩ := a.recover P hP
    exact ⟨Q, hQ, hcostQ.trans hcostP, fun x y h => hreachQ x y (hreachP _ _ h)⟩

/-- Changing only edge-set presentations preserves the actual vertex embedding. -/
noncomputable def congr {E E' : Finset (Sym2 V)} {c : Sym2 V → ℝ}
    {F F' : Finset (Sym2 W)} {d : Sym2 W → ℝ}
    (cert : ZoneSubdivisionCertificate E c F d) (hE : E = E') (hF : F = F') :
    ZoneSubdivisionCertificate E' c F' d where
  vertices := cert.vertices
  cost_eq := by subst E'; subst F'; exact cert.cost_eq
  realize {a b} p := by subst E'; subst F'; exact cert.realize p
  recover H hH := by subst E'; subst F'; exact cert.recover H hH

noncomputable def midpoint [DecidableEq V] (E : Finset (Sym2 V)) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ E, 0 ≤ c e) (hnd : ∀ e ∈ E, ¬e.IsDiag) :
    ZoneSubdivisionCertificate E c (E.biUnion zoneSplitEdges) (zoneHalfCost c) where
  vertices := Function.Embedding.inl
  cost_eq := zoneSplitUnion_cost E c hnd
  realize p := ⟨zoneExpandWalk E p, zoneExpandWalk_cost E c p⟩
  recover H hH := ⟨zoneRecombine E H, Finset.filter_subset _ _, zoneRecombine_cost E c hc hnd H hH,
    fun _ _ h => zoneRecombine_reachable hH h⟩

end ZoneSubdivisionCertificate
end OnlineSteinerForest.UpperBound
