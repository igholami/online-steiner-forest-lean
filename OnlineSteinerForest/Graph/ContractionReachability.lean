import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! Reachability under graph contraction by an arbitrary vertex map. -/
namespace OnlineSteinerForest

variable {V W : Type*}

theorem reachable_map_vertices (G : SimpleGraph V) (f : V → W) {u v : V}
    (h : G.Reachable u v) : (G.map f).Reachable (f u) (f v) := by
  classical
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons u v z huv p ih =>
    by_cases hsame : f u = f v
    · rw [hsame]; exact ih
    · exact (SimpleGraph.map_adj_apply' huv hsame).reachable.trans ih

theorem reachable_from_edge_routes (H : SimpleGraph W) (G : SimpleGraph V) (root : W → V)
    (hroutes : ∀ a b, H.Adj a b → G.Reachable (root a) (root b))
    {a b : W} (h : H.Reachable a b) : G.Reachable (root a) (root b) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact .refl _
  | @cons a b z hab p ih => exact (hroutes a b hab).trans ih

/-- Contracting connected fibers preserves exactly the original connections. -/
theorem contraction_reachable_iff (G : SimpleGraph V) (f : V → W) (root : W → V)
    (hfiber : ∀ v, G.Reachable v (root (f v))) (u v : V) :
    (G.map f).Reachable (f u) (f v) ↔ G.Reachable u v := by
  constructor
  · intro h
    have hroot : G.Reachable (root (f u)) (root (f v)) := by
      apply reachable_from_edge_routes (G.map f) G root ?_ h
      intro a b hab
      obtain ⟨_, x, y, hxy, hxa, hyb⟩ := (SimpleGraph.map_adj' f G a b).mp hab
      have hx := hfiber x
      have hy := hfiber y
      rw [hxa] at hx
      rw [hyb] at hy
      exact hx.symm.trans (hxy.reachable.trans hy)
    exact (hfiber u).trans (hroot.trans (hfiber v).symm)
  · exact reachable_map_vertices G f

end OnlineSteinerForest
