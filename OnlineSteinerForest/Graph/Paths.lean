import OnlineSteinerForest.Graph.Cost

/-! Finite shortest-path search, retaining standard `SimpleGraph.Walk.IsPath`. -/
namespace OnlineSteinerForest

universe u

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An edge set is a candidate precisely when it is the edge set of a simple path. -/
def IsPathEdges (G : SimpleGraph V) (s t : V) (F : Finset (Sym2 V)) : Prop :=
  ∃ p : G.Walk s t, p.IsPath ∧ p.edges.toFinset = F

/-- All candidate paths, represented by their edge sets. -/
noncomputable def pathCandidates (G : SimpleGraph V) (s t : V) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact Finset.univ.filter (IsPathEdges G s t)

@[simp] theorem mem_pathCandidates (G : SimpleGraph V) (s t : V)
    (F : Finset (Sym2 V)) : F ∈ pathCandidates G s t ↔ IsPathEdges G s t F := by
  classical
  simp [pathCandidates]

/-- Feasibility supplies at least one candidate, including the empty path for `s = t`. -/
theorem pathCandidates_nonempty (G : SimpleGraph V) {s t : V}
    (h : G.Reachable s t) : (pathCandidates G s t).Nonempty := by
  classical
  obtain ⟨p⟩ := h
  exact ⟨p.toPath.val.edges.toFinset, mem_pathCandidates _ _ _ _ |>.2
    ⟨p.toPath.val, p.toPath.property, rfl⟩⟩

/-- An arbitrary rule selecting a minimum residual-cost simple path, across finite graphs. -/
class PathSelection where
  choose : ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s t : V), G.Reachable s t → Finset (Sym2 V)
  spec : ∀ {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (c : Sym2 V → ℝ) (B : Finset (Sym2 V))
    (s t : V) (h : G.Reachable s t),
    IsPathEdges G s t (choose G c B s t h) ∧
      ∀ F, IsPathEdges G s t F → residualCost c B (choose G c B s t h) ≤ residualCost c B F

/-- Classical finite minimization supplies the default tie rule. -/
noncomputable instance (priority := 100) canonicalPathSelection : PathSelection where
  choose G c B s t h := Classical.choose ((pathCandidates G s t).exists_min_image
    (residualCost c B) (pathCandidates_nonempty G h))
  spec G c B s t h := by
    classical
    obtain ⟨hm, hmin⟩ := Classical.choose_spec ((pathCandidates G s t).exists_min_image
      (residualCost c B) (pathCandidates_nonempty G h))
    exact ⟨(mem_pathCandidates _ _ _ _).1 hm,
      fun F hF => hmin F ((mem_pathCandidates _ _ _ _).2 hF)⟩

variable [PathSelection]

/-- A minimum residual-cost simple path, using the supplied arbitrary tie rule. -/
noncomputable def shortestPathEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) : Finset (Sym2 V) :=
  PathSelection.choose G c B s t h

/-- The implementation chooses an actual path and minimizes incremental purchase cost. -/
theorem shortestPathEdges_spec (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (B : Finset (Sym2 V)) (s t : V) (h : G.Reachable s t) :
    IsPathEdges G s t (shortestPathEdges G c B s t h) ∧
      ∀ F, IsPathEdges G s t F →
        residualCost c B (shortestPathEdges G c B s t h) ≤ residualCost c B F :=
  PathSelection.spec G c B s t h

end OnlineSteinerForest
