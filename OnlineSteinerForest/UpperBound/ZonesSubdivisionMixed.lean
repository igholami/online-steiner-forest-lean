import OnlineSteinerForest.UpperBound.ZonesSubdivisionCertificate
import OnlineSteinerForest.UpperBound.ZonesPartitionConnected

/-! Recovery remains valid after adjoining arbitrary auxiliary edges on original vertices. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Reference components can be replaced separately while all original auxiliary edges stay. -/
theorem reachable_mixed_union (f : V ↪ W) (H : Finset (Sym2 W)) (P K : Finset (Sym2 V))
    (htransfer : ∀ u v, (SimpleGraph.fromEdgeSet (H : Set (Sym2 W))).Reachable (f u) (f v) →
      (SimpleGraph.fromEdgeSet (P : Set (Sym2 V))).Reachable u v)
    {a b : V} (hab : (SimpleGraph.fromEdgeSet
      ((H ∪ K.image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W))).Reachable (f a) (f b)) :
    (SimpleGraph.fromEdgeSet ((P ∪ K : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b := by
  let O := SimpleGraph.fromEdgeSet ((P ∪ K : Finset (Sym2 V)) : Set (Sym2 V))
  let A : W → Prop := fun w => ∃ z : V, O.Reachable a z ∧
    (SimpleGraph.fromEdgeSet (H : Set (Sym2 W))).Reachable (f z) w
  have hold (u v : V) (huv : s(u, v) ∈ K) (hu : A (f u)) : A (f v) := by
    obtain ⟨z, haz, hzu⟩ := hu
    have hzu' : O.Reachable z u := (htransfer z u hzu).mono (fromEdges_mono Finset.subset_union_left)
    have huv' : O.Reachable u v := by
      by_cases hne : u = v
      · subst v; exact .refl _
      · exact (show O.Adj u v from ⟨Finset.mem_union_right _ huv, hne⟩).reachable
    exact ⟨v, haz.trans (hzu'.trans huv'), .refl _⟩
  have haux : ∀ e ∈ K, ∀ x y, Sym2.map f e = s(x, y) → A x → A y := by
    intro e
    refine Sym2.ind (fun u v he x y heq hx => ?_) e
    rcases Sym2.eq_iff.mp heq with ⟨hx', hy'⟩ | ⟨hy', hx'⟩
    · rw [← hx'] at hx
      rw [← hy']
      exact hold u v he hx
    · rw [← hx'] at hx
      rw [← hy']
      exact hold v u (by simpa only [Sym2.eq_swap] using he) hx
  have hclosed : ∀ x y, (SimpleGraph.fromEdgeSet
      ((H ∪ K.image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W))).Adj x y → A x → A y := by
    intro x y hxy hx
    rcases Finset.mem_union.mp hxy.1 with heH | heK
    · obtain ⟨z, haz, hzx⟩ := hx
      exact ⟨z, haz, hzx.trans (show (SimpleGraph.fromEdgeSet (H : Set (Sym2 W))).Adj x y from
        ⟨heH, hxy.2⟩).reachable⟩
    · obtain ⟨e, he, heq⟩ := Finset.mem_image.mp heK
      exact haux e he x y heq hx
  obtain ⟨p⟩ := hab
  have hprop : ∀ {x y}, (SimpleGraph.fromEdgeSet
      ((H ∪ K.image (Sym2.map f) : Finset (Sym2 W)) : Set (Sym2 W))).Walk x y → A x → A y := by
    intro x y q
    induction q with
    | nil => exact id
    | cons hxy q ih => exact fun hx => ih (hclosed _ _ hxy hx)
  obtain ⟨z, haz, hzb⟩ := hprop p ⟨a, .refl _, .refl _⟩
  exact haz.trans ((htransfer z b hzb).mono (fromEdges_mono Finset.subset_union_left))

/-- Recover whole original reference edges while retaining arbitrary original auxiliary edges. -/
theorem ZoneSubdivisionCertificate.recover_mixed {E : Finset (Sym2 V)} {c : Sym2 V → ℝ}
    {F : Finset (Sym2 W)} {d : Sym2 W → ℝ} (cert : ZoneSubdivisionCertificate E c F d)
    (H : Finset (Sym2 W)) (hH : H ⊆ F) (K : Finset (Sym2 V)) :
    ∃ P : Finset (Sym2 V), P ⊆ E ∧ edgeCost c P ≤ edgeCost d H ∧ ∀ a b : V,
      (SimpleGraph.fromEdgeSet
        ((H ∪ K.image (Sym2.map cert.vertices) : Finset (Sym2 W)) : Set (Sym2 W))).Reachable
        (cert.vertices a) (cert.vertices b) →
      (SimpleGraph.fromEdgeSet ((P ∪ K : Finset (Sym2 V)) : Set (Sym2 V))).Reachable a b := by
  obtain ⟨P, hP, hcost, hreach⟩ := cert.recover H hH
  exact ⟨P, hP, hcost, fun _ _ h => reachable_mixed_union cert.vertices H P K hreach h⟩

end OnlineSteinerForest.UpperBound
