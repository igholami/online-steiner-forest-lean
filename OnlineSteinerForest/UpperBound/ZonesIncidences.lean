import OnlineSteinerForest.UpperBound.ZonesHubDegree

/-! Turning terminal-degree bounds into a finite number of zone attachment paths. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical BigOperators

/-- Every edge incident to a hub is charged to a hub incidence. -/
theorem hub_incident_edge_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hubs : Finset V) :
    (hubs.biUnion (fun v => G.incidenceFinset v)).card ≤ ∑ v ∈ hubs, G.degree v := by
  simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using
    (Finset.card_biUnion_le (s := hubs) (t := fun v => G.incidenceFinset v))

/-- A terminal-spanning tree needs fewer than twice as many attachments as
required vertices, even when some edges touch two hubs. -/
theorem hub_attachment_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (hubs terminals : Finset V)
    (hsub : hubs ⊆ terminals) (hdegree : ∀ v ∉ terminals, 2 ≤ G.degree v) :
    (hubs.biUnion (fun v => G.incidenceFinset v)).card + 2 ≤ 2 * terminals.card := by
  have hcount := hub_incident_edge_count G hubs
  have hbound := hub_degree_sum_bound G hG hubs terminals hsub hdegree
  omega

end OnlineSteinerForest.UpperBound
