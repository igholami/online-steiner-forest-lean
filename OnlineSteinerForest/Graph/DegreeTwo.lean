import OnlineSteinerForest.Graph.Paths

/-! Simple paths through a private degree-two subdivision vertex. -/
namespace OnlineSteinerForest

variable [OnlineSteinerForest.PathSelection]

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A simple `u`--`v` path using `u`--`x`, where `x` has just the two possible
neighbors `u,v`, is exactly the two-edge path through `x`. -/
theorem path_edges_eq_pair_of_mem {u v x : V} (huv : u ≠ v) (hxv : x ≠ v)
    (hdeg : ∀ z, G.Adj x z → z = u ∨ z = v)
    (p : G.Walk u v) (hp : p.IsPath) (hmem : s(u, x) ∈ p.edges) :
    p.edges.toFinset = {s(u, x), s(x, v)} := by
  obtain ⟨y, huy, q, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne huv p
  have hxy : x = y := by simpa using hp.eq_snd_of_mem_edges hmem
  subst y
  obtain ⟨z, hxz, r, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne hxv q
  rcases hdeg z hxz with rfl | rfl
  · simp [SimpleGraph.Walk.cons_isPath_iff, SimpleGraph.Walk.support_cons] at hp
  · have hr : r.IsPath := hp.of_cons.of_cons
    have hrnil : r.Nil := hr.nil_iff_eq.mpr rfl
    cases hrnil
    simp

/-- Using either edge incident to the private vertex forces the same two-edge path. -/
theorem path_edges_eq_pair_of_mem_either {u v x : V} (huv : u ≠ v)
    (hxu : x ≠ u) (hxv : x ≠ v)
    (hdeg : ∀ z, G.Adj x z → z = u ∨ z = v)
    (p : G.Walk u v) (hp : p.IsPath)
    (hmem : s(u, x) ∈ p.edges ∨ s(x, v) ∈ p.edges) :
    p.edges.toFinset = {s(u, x), s(x, v)} := by
  rcases hmem with hmem | hmem
  · exact path_edges_eq_pair_of_mem huv hxv hdeg p hp hmem
  · have hrev : s(v, x) ∈ p.reverse.edges := by
      simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse, Sym2.eq_swap] using hmem
    have heq := path_edges_eq_pair_of_mem huv.symm hxu
      (fun z hz => (hdeg z hz).symm) p.reverse hp.reverse hrev
    simpa [Sym2.eq_swap, Finset.pair_comm] using heq

end OnlineSteinerForest
