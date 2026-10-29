import OnlineSteinerForest.Graph.Cost

/-! A rooted expression for assembling an ordinary finite tree from edges and branches. -/
namespace OnlineSteinerForest.UpperBound

open scoped Classical

inductive ZoneTree (V : Type*) : V → Type _
  | leaf (r : V) : ZoneTree V r
  | extend (r s : V) (child : ZoneTree V s) : ZoneTree V r
  | join (r : V) (left right : ZoneTree V r) : ZoneTree V r

namespace ZoneTree
variable {V W : Type*} [DecidableEq V] [DecidableEq W]

def vertices {r : V} : ZoneTree V r → Finset V
  | .leaf r => {r}
  | .extend r _ t => insert r t.vertices
  | .join _ a b => a.vertices ∪ b.vertices

def edges {r : V} : ZoneTree V r → Finset (Sym2 V)
  | .leaf _ => ∅
  | .extend r s t => insert s(r, s) t.edges
  | .join _ a b => a.edges ∪ b.edges

theorem root_mem {r : V} (t : ZoneTree V r) : r ∈ t.vertices := by
  induction t with
  | leaf => simp [vertices]
  | extend => simp [vertices]
  | join _ a b ha _ => simp [vertices, ha]

def map (f : V → W) {r : V} : ZoneTree V r → ZoneTree W (f r)
  | .leaf r => .leaf (f r)
  | .extend r s t => .extend (f r) (f s) (t.map f)
  | .join r a b => .join (f r) (a.map f) (b.map f)

@[simp] theorem vertices_map (f : V → W) {r : V} (t : ZoneTree V r) :
    (t.map f).vertices = t.vertices.image f := by
  induction t with
  | leaf => simp [map, vertices]
  | extend _ _ _ ht => simp [map, vertices, ht]
  | join _ _ _ ha hb => simp [map, vertices, ha, hb, Finset.image_union]

@[simp] theorem edges_map (f : V → W) {r : V} (t : ZoneTree V r) :
    (t.map f).edges = t.edges.image (Sym2.map f) := by
  induction t with
  | leaf => simp [map, edges]
  | extend _ _ _ ht => simp [map, edges, ht]
  | join _ _ _ ha hb => simp [map, edges, ha, hb, Finset.image_union]

/-- Attach a new leaf at any vertex already present in the rooted expression. -/
noncomputable def graft {r : V} (t : ZoneTree V r) (u v : V) (hu : u ∈ t.vertices) : ZoneTree V r :=
  match t with
  | .leaf r => .join r (.leaf r) (.extend r v (.leaf v))
  | .extend r s t => if h : u = r then
      .join r (.extend r s t) (.extend r v (.leaf v))
    else .extend r s (t.graft u v (by simpa [vertices, h] using hu))
  | .join r a b => if h : u ∈ a.vertices then .join r (a.graft u v h) b
    else .join r a (b.graft u v (by simpa [vertices, h] using hu))

@[simp] theorem vertices_graft {r : V} (t : ZoneTree V r) (u v : V) (hu : u ∈ t.vertices) :
    (t.graft u v hu).vertices = insert v t.vertices := by
  induction t with
  | leaf r =>
    ext x
    simp [graft, vertices, or_comm]
  | extend r s t ih =>
    simp only [graft]
    split_ifs with h
    · simp [vertices, Finset.insert_union, Finset.insert_comm]
    · simp [vertices, ih, Finset.insert_comm]
  | join r a b ha hb =>
    simp only [graft]
    split_ifs with h
    · simp [vertices, ha, Finset.insert_union]
    · simp [vertices, hb, Finset.union_insert]

@[simp] theorem edges_graft {r : V} (t : ZoneTree V r) (u v : V) (hu : u ∈ t.vertices) :
    (t.graft u v hu).edges = insert s(u, v) t.edges := by
  induction t with
  | leaf r =>
    have he : u = r := by simpa [vertices] using hu
    subst u
    simp [graft, edges]
  | extend r s t ih =>
    simp only [graft]
    split_ifs with h
    · subst u; simp [edges, Finset.insert_union, Finset.insert_comm]
    · simp [edges, ih, Finset.insert_comm]
  | join r a b ha hb =>
    simp only [graft]
    split_ifs with h
    · simp [edges, ha, Finset.insert_union]
    · simp [edges, hb, Finset.union_insert]

end ZoneTree
end OnlineSteinerForest.UpperBound
