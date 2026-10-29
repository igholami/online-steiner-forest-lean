import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! Adding any family of leaves to an embedded forest preserves acyclicity. -/
namespace OnlineSteinerForest.UpperBound

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem cycle_vertex_has_two_neighbors {z w : W} (c : H.Walk z z) (hc : c.IsCycle)
    (hw : w ∈ c.support) : ∃ a b, H.Adj w a ∧ H.Adj w b ∧ a ≠ b := by
  classical
  let p := c.rotate w hw
  have hp : p.IsCycle := hc.rotate hw
  exact ⟨p.snd, p.penultimate, p.adj_snd hp.not_nil, (p.adj_penultimate hp.not_nil).symm,
    hp.snd_ne_penultimate⟩

theorem isAcyclic_leaf_extension (f : G ↪g H) (hG : G.IsAcyclic)
    (hleaf : ∀ w ∉ Set.range f, ∀ a b, H.Adj w a → H.Adj w b → a = b) : H.IsAcyclic := by
  classical
  intro z c hc
  have hall : ∀ w ∈ c.support, w ∈ Set.range f := by
    intro w hw
    by_contra hn
    obtain ⟨a, b, ha, hb, hab⟩ := cycle_vertex_has_two_neighbors c hc hw
    exact hab (hleaf w hn a b ha hb)
  let p := c.induce (Set.range f) hall
  have hp : p.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map (f := (SimpleGraph.Embedding.induce (Set.range f)).toHom)
    simpa [p] using hc
  let q := p.map f.isoInduceRange.symm.toHom
  have hq : q.IsCycle := hp.map f.isoInduceRange.symm.injective
  exact hG q hq

end OnlineSteinerForest.UpperBound
