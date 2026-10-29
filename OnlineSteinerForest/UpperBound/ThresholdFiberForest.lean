import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! A graph with forest fibers and no edges between fibers is a forest. -/
namespace OnlineSteinerForest.UpperBound

variable {V Z : Type*} {G : SimpleGraph V}

theorem walk_support_fiber (f : V → Z) (hadj : ∀ u v, G.Adj u v → f u = f v)
    {u v : V} (p : G.Walk u v) : ∀ w ∈ p.support, f w = f u := by
  induction p with
  | @nil a =>
    intro w hw
    have hh : w = a := by simpa using hw
    exact congrArg f hh
  | @cons u v z huv p ih =>
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · rfl
    · exact (ih w hw).trans (hadj u v huv).symm

theorem isAcyclic_of_fibers (f : V → Z) (hadj : ∀ u v, G.Adj u v → f u = f v)
    (hfiber : ∀ z, (G.induce {v | f v = z}).IsAcyclic) : G.IsAcyclic := by
  intro z c hc
  have hall := walk_support_fiber f hadj c
  let p := c.induce {v | f v = f z} hall
  have hp : p.IsCycle := by
    apply SimpleGraph.Walk.IsCycle.of_map
      (f := (SimpleGraph.Embedding.induce {v | f v = f z}).toHom)
    simpa [p] using hc
  exact hfiber (f z) p hp

end OnlineSteinerForest.UpperBound
