import OnlineSteinerForest.UpperBound.GirthEndpointGraph

/-! Restriction of labelled edges and vertices to one standard connected component. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V I : Type*}

noncomputable instance [Finite V] (left right : I → V) :
    Fintype (endpointGraph left right).ConnectedComponent := Fintype.ofFinite _

abbrev ComponentVertices (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) := C.supp
abbrev ComponentEdges (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :=
  {i : I // (endpointGraph left right).connectedComponentMk (left i) = C}

noncomputable instance [Finite V] (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :
    Fintype (ComponentVertices left right C) := Fintype.ofFinite _
noncomputable instance [Finite I] (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :
    Fintype (ComponentEdges left right C) := Fintype.ofFinite _

def componentLeft (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :
    ComponentEdges left right C → ComponentVertices left right C := fun i => ⟨left i, i.property⟩

def componentRight (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :
    ComponentEdges left right C → ComponentVertices left right C := fun i => ⟨right i,
      (SimpleGraph.ConnectedComponent.sound (dart_endpoint_reachable left right (i.val, false))).symm.trans i.property⟩

theorem leftComponent_eq_tail (left right : I → V) (d : Dart I) :
    (endpointGraph left right).connectedComponentMk (left d.1) =
      (endpointGraph left right).connectedComponentMk (tail left right d) := by
  rcases d with ⟨i, b⟩
  cases b
  · rfl
  · exact SimpleGraph.ConnectedComponent.sound (dart_endpoint_reachable left right (i, false))

theorem component_endpointGraph (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :
    endpointGraph (componentLeft left right C) (componentRight left right C) = C.toSimpleGraph := by
  ext x y
  change (x ≠ y ∧ ∃ d : Dart (ComponentEdges left right C),
    tail _ _ d = x ∧ head _ _ d = y) ↔ (endpointGraph left right).Adj x.val y.val
  constructor
  · rintro ⟨hne, ⟨i, b⟩, ht, hh⟩
    refine ⟨fun h => hne (Subtype.ext h), (i.val, b), ?_, ?_⟩
    · have heq := congrArg Subtype.val ht
      cases b <;> exact heq
    · have heq := congrArg Subtype.val hh
      cases b <;> exact heq
  · rintro ⟨hne, d, ht, hh⟩
    have hi : (endpointGraph left right).connectedComponentMk (left d.1) = C := by
      rw [leftComponent_eq_tail, ht]
      exact x.property
    refine ⟨fun h => hne (congrArg Subtype.val h), (⟨d.1, hi⟩, d.2), ?_, ?_⟩
    · apply Subtype.ext
      cases hb : d.2 <;> simpa [tail, componentLeft, componentRight, hb] using ht
    · apply Subtype.ext
      cases hb : d.2 <;> simpa [head, componentLeft, componentRight, hb] using hh

theorem component_endpoint_connected (left right : I → V) (C : (endpointGraph left right).ConnectedComponent) :
    (endpointGraph (componentLeft left right C) (componentRight left right C)).Connected := by
  rw [component_endpointGraph]
  exact C.connected_toSimpleGraph

end OnlineSteinerForest.UpperBound.Girth
