import OnlineSteinerForest.Graph.Relabel
import OnlineSteinerForest.Graph.Optimum

/-! Feasible offline solutions retain their cost under graph isomorphisms. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def relabelRequests (e : V ≃ W) (xs : List (V × V)) : List (W × W) :=
  xs.map (fun q => (e q.1, e q.2))

omit [DecidableEq V] [DecidableEq W] in
theorem requests_relabel_feasible {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (xs : List (V × V))
    (hx : ∀ q ∈ xs, G.Reachable q.1 q.2) :
    ∀ q ∈ relabelRequests f.toEquiv xs, H.Reachable q.1 q.2 := by
  intro q hq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
  exact (hx r hr).map f.toHom

omit [DecidableEq V] [DecidableEq W] in
theorem FeasibleEdges.relabel {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (xs : List (V × V)) (F : Finset (Sym2 V))
    (hF : FeasibleEdges G xs F) :
    FeasibleEdges H (relabelRequests f.toEquiv xs) (relabelEdges f.toEquiv F) := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact (f.map_mem_edgeSet_iff).mpr (hF.1 y hy)
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    let g : SimpleGraph.fromEdgeSet (F : Set (Sym2 V)) →g
        SimpleGraph.fromEdgeSet (relabelEdges f.toEquiv F : Set (Sym2 W)) :=
      { toFun := f
        map_rel' := by
          intro u v huv
          refine ⟨?_, f.injective.ne huv.2⟩
          exact Finset.mem_map.mpr ⟨s(u, v), huv.1, rfl⟩ }
    exact (hF.2 r hr).map g

variable [Fintype V] [Fintype W]

theorem optimum_relabel_le {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (c : Sym2 V → ℝ) (xs : List (V × V))
    (hx : ∀ q ∈ xs, G.Reachable q.1 q.2)
    (hy : ∀ q ∈ relabelRequests f.toEquiv xs, H.Reachable q.1 q.2) :
    optimum H (relabelCost f.toEquiv c) (relabelRequests f.toEquiv xs) hy ≤ optimum G c xs hx := by
  calc
    _ ≤ edgeCost (relabelCost f.toEquiv c)
        (relabelEdges f.toEquiv (optimalEdges G c xs hx)) :=
      optimum_le _ _ _ _ _ ((optimalEdges_feasible G c xs hx).relabel f xs _)
    _ = _ := edgeCost_relabel _ _ _

omit [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] in
@[simp] theorem relabelCost_symm (e : V ≃ W) (c : Sym2 V → ℝ) :
    relabelCost e.symm (relabelCost e c) = c := by
  funext x
  simp [relabelCost, edgeEquiv, Function.comp_def, Sym2.map_map]

omit [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W] in
@[simp] theorem relabelRequests_symm (e : V ≃ W) (xs : List (V × V)) :
    relabelRequests e.symm (relabelRequests e xs) = xs := by
  simp [relabelRequests, List.map_map, Function.comp_def]

theorem optimum_relabel_eq {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (c : Sym2 V → ℝ) (xs : List (V × V))
    (hx : ∀ q ∈ xs, G.Reachable q.1 q.2)
    (hy : ∀ q ∈ relabelRequests f.toEquiv xs, H.Reachable q.1 q.2) :
    optimum H (relabelCost f.toEquiv c) (relabelRequests f.toEquiv xs) hy = optimum G c xs hx := by
  apply le_antisymm (optimum_relabel_le f c xs hx hy)
  have hback := optimum_relabel_le f.symm (relabelCost f.toEquiv c)
    (relabelRequests f.toEquiv xs) hy
    (requests_relabel_feasible f.symm _ hy)
  simpa only [show f.symm.toEquiv = f.toEquiv.symm from rfl,
    relabelCost_symm, relabelRequests_symm] using hback

end OnlineSteinerForest
