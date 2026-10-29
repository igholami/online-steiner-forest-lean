import OnlineSteinerForest.UpperBound.GirthComponentRestriction
import OnlineSteinerForest.UpperBound.GirthConnectedCounting

/-! Vertex, edge, cost, and cycle-rank sums over standard connected components. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem sum_component_vertices (left right : I → V) :
    (∑ C : (endpointGraph left right).ConnectedComponent, Fintype.card (ComponentVertices left right C)) =
      Fintype.card V := by
  classical
  have hh := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset V)
    (Finset.univ : Finset (endpointGraph left right).ConnectedComponent)
    (endpointGraph left right).connectedComponentMk
  have hv : ∀ C : (endpointGraph left right).ConnectedComponent,
      Fintype.card (ComponentVertices left right C) =
        (Finset.univ.filter (fun x => (endpointGraph left right).connectedComponentMk x = C)).card := by
    intro C
    exact @Fintype.card_subtype V _ (fun x => (endpointGraph left right).connectedComponentMk x = C)
      (inferInstance : Fintype ↑(ComponentVertices left right C)) _
  simp_rw [hv]
  simpa using hh

theorem sum_component_edges (left right : I → V) :
    (∑ C : (endpointGraph left right).ConnectedComponent, Fintype.card (ComponentEdges left right C)) =
      Fintype.card I := by
  classical
  have hh := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset I)
    (Finset.univ : Finset (endpointGraph left right).ConnectedComponent)
    (fun i => (endpointGraph left right).connectedComponentMk (left i))
  simpa [ComponentEdges, Fintype.card_subtype] using hh

theorem sum_component_costs (left right : I → V) (w : I → ℝ) :
    (∑ C : (endpointGraph left right).ConnectedComponent, ∑ i : ComponentEdges left right C, w i.val) = ∑ i, w i := by
  classical
  calc
    _ = ∑ C : (endpointGraph left right).ConnectedComponent,
        ∑ i ∈ Finset.univ.filter (fun i => (endpointGraph left right).connectedComponentMk (left i) = C), w i := by
      apply Finset.sum_congr rfl
      intro C _
      exact (Finset.sum_subtype _ (by intro i; simp [ComponentEdges]) w).symm
    _ = _ := by
      simpa using Finset.sum_fiberwise_eq_sum_filter (Finset.univ : Finset I)
        (Finset.univ : Finset (endpointGraph left right).ConnectedComponent)
        (fun i => (endpointGraph left right).connectedComponentMk (left i)) w

theorem sum_component_ranks (left right : I → V) :
    (∑ C : (endpointGraph left right).ConnectedComponent,
      cycleRank (componentLeft left right C) (componentRight left right C)) = cycleRank left right := by
  have hh := congrArg (fun f : (endpointGraph left right).ConnectedComponent → ℕ => ∑ C, f C)
    (funext (fun C => connected_rank_identity (componentLeft left right C) (componentRight left right C)
      (component_endpoint_connected left right C)))
  simp only [Finset.sum_add_distrib, sum_component_vertices, sum_component_edges, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, mul_one] at hh
  have hc : componentCount left right = Fintype.card (endpointGraph left right).ConnectedComponent := by
    exact (Nat.card_congr (endpointComponentEquiv left right)).trans Nat.card_eq_fintype_card
  change (∑ C : (endpointGraph left right).ConnectedComponent,
    cycleRank (componentLeft left right C) (componentRight left right C)) =
      Fintype.card I + componentCount left right - Fintype.card V
  omega

end OnlineSteinerForest.UpperBound.Girth
