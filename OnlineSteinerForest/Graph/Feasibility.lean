import OnlineSteinerForest.Graph.Paths

/-! Feasibility is ordinary reachability in the graph formed by purchased edges. -/
namespace OnlineSteinerForest

variable {V : Type*} [DecidableEq V]

/-- `F` uses only input edges and connects every requested pair. -/
def FeasibleEdges (G : SimpleGraph V) (requests : List (V × V))
    (F : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ F, e ∈ G.edgeSet) ∧
    ∀ q ∈ requests, (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable q.1 q.2

/-- The edge set of a standard path is contained in the input graph. -/
theorem IsPathEdges.subset_edgeSet {G : SimpleGraph V} {s t : V}
    {F : Finset (Sym2 V)} (h : IsPathEdges G s t F) :
    ∀ e ∈ F, e ∈ G.edgeSet := by
  obtain ⟨p, _, rfl⟩ := h
  intro e he
  exact p.edges_subset_edgeSet (List.mem_toFinset.mp he)

omit [DecidableEq V] in
/-- A path remains a walk in the graph formed by any superset of its edges. -/
theorem walk_reachable_fromEdgeSet {G : SimpleGraph V} {s t : V}
    (p : G.Walk s t) (F : Finset (Sym2 V))
    (h : ∀ e ∈ p.edges, e ∈ F) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t := by
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | @cons u v w huv p ih =>
    have huv' : (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Adj u v := by
      exact ⟨h _ (by simp), huv.ne⟩
    exact SimpleGraph.Adj.reachable huv' |>.trans (ih (fun e he => h e (by simp [he])))

theorem IsPathEdges.reachable {G : SimpleGraph V} {s t : V}
    {F : Finset (Sym2 V)} (h : IsPathEdges G s t F) :
    (SimpleGraph.fromEdgeSet (F : Set (Sym2 V))).Reachable s t := by
  obtain ⟨p, _, rfl⟩ := h
  exact walk_reachable_fromEdgeSet p _ (by simp)

end OnlineSteinerForest
