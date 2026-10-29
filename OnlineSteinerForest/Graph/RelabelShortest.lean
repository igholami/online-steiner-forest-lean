import OnlineSteinerForest.Graph.Relabel

/-! A unique minimizing path transports independently of classical tie breaking. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

omit [Fintype V] in
theorem shortestPathEdges_map_of_unique {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) (c : Sym2 V → ℝ) (B F : Finset (Sym2 V)) (s t : V)
    (hF : IsPathEdges G s t F)
    (hunique : ∀ D, IsPathEdges G s t D → residualCost c B D ≤ residualCost c B F → D = F)
    (hreach : H.Reachable (f s) (f t)) :
    shortestPathEdges H (relabelCost f.toEquiv c) (relabelEdges f.toEquiv B)
      (f s) (f t) hreach = relabelEdges f.toEquiv F := by
  let P := shortestPathEdges H (relabelCost f.toEquiv c) (relabelEdges f.toEquiv B)
    (f s) (f t) hreach
  have hs := shortestPathEdges_spec H (relabelCost f.toEquiv c)
    (relabelEdges f.toEquiv B) (f s) (f t) hreach
  let D := relabelEdges f.toEquiv.symm P
  have hD : IsPathEdges G s t D := by
    have hback := hs.1.mapIso f.symm
    change IsPathEdges G (f.symm (f s)) (f.symm (f t)) D at hback
    simpa only [RelIso.symm_apply_apply] using hback
  have hP : relabelEdges f.toEquiv D = P := relabelEdges_symm _ _
  have hle : residualCost c B D ≤ residualCost c B F := by
    have h := hs.2 _ (hF.mapIso f)
    change residualCost (relabelCost f.toEquiv c) (relabelEdges f.toEquiv B) P ≤ _ at h
    rw [← hP, residualCost_relabel, residualCost_relabel] at h
    exact h
  have heq := hunique D hD hle
  rw [heq] at hP
  exact hP.symm

end OnlineSteinerForest
