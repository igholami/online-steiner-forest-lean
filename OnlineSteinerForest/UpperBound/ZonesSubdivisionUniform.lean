import OnlineSteinerForest.UpperBound.ZonesSubdivisionProperties
import OnlineSteinerForest.UpperBound.ZonesSubdivisionCertificate

/-! Deterministic global subdivision operators shared by all reference components. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
universe u

def subdivisionVertices (V : Type u) : ℕ → Type u
  | 0 => V
  | n + 1 => ZoneSubdivisionVertex (subdivisionVertices V n)

instance subdivisionFintype {V : Type u} [Fintype V] : (n : ℕ) → Fintype (subdivisionVertices V n)
  | 0 => inferInstanceAs (Fintype V)
  | n + 1 => by
    letI := subdivisionFintype (V := V) n
    exact inferInstanceAs (Fintype (ZoneSubdivisionVertex (subdivisionVertices V n)))

instance subdivisionDecidableEq {V : Type u} [DecidableEq V] : (n : ℕ) → DecidableEq (subdivisionVertices V n)
  | 0 => inferInstanceAs (DecidableEq V)
  | n + 1 => by
    letI := subdivisionDecidableEq (V := V) n
    exact inferInstanceAs (DecidableEq (ZoneSubdivisionVertex (subdivisionVertices V n)))

def subdivisionEdges {V : Type u} [DecidableEq V] (E : Finset (Sym2 V)) :
    (n : ℕ) → Finset (Sym2 (subdivisionVertices V n))
  | 0 => E
  | n + 1 => (subdivisionEdges E n).biUnion zoneSplitEdges

noncomputable def subdivisionCost {V : Type u} (c : Sym2 V → ℝ) :
    (n : ℕ) → Sym2 (subdivisionVertices V n) → ℝ
  | 0 => c
  | n + 1 => zoneHalfCost (subdivisionCost c n)

def subdivisionEmbedding (V : Type u) : (n : ℕ) → V ↪ subdivisionVertices V n
  | 0 => Function.Embedding.refl _
  | n + 1 => (subdivisionEmbedding V n).trans Function.Embedding.inl

def subdivisionShape {V : Type u} {r : V} (t : ZoneTree V r) :
    (n : ℕ) → ZoneTree (subdivisionVertices V n) (subdivisionEmbedding V n r)
  | 0 => t
  | n + 1 => (subdivisionShape t n).subdivide

@[simp] theorem subdivisionShape_edges {V : Type u} [DecidableEq V] {r : V} (t : ZoneTree V r) (n : ℕ) :
    (subdivisionShape t n).edges = subdivisionEdges t.edges n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (subdivisionShape t n).subdivide.edges = _
    rw [ZoneTree.edges_subdivide, ih]
    rfl

theorem subdivisionEdges_mono {V : Type u} [DecidableEq V] {E F : Finset (Sym2 V)}
    (hEF : E ⊆ F) (n : ℕ) : subdivisionEdges E n ⊆ subdivisionEdges F n := by
  induction n with
  | zero => exact hEF
  | succ n ih =>
    intro e he
    obtain ⟨f, hf, he⟩ := Finset.mem_biUnion.mp he
    exact Finset.mem_biUnion.mpr ⟨f, ih hf, he⟩

end OnlineSteinerForest.UpperBound
