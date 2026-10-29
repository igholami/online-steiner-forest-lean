import OnlineSteinerForest.UpperBound.GirthCollision

/-! Label-injective embeddings transport collision witnesses with exact cost. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {V W I J : Type*}

def mapDart (f : J → I) (a : Dart J) : Dart I := (f a.1, a.2)

theorem mapDart_injective (f : J → I) (hf : Function.Injective f) : Function.Injective (mapDart f) := by
  intro a b h
  have hl := congrArg Prod.fst h
  have hb := congrArg Prod.snd h
  exact Prod.ext (hf hl) hb

theorem mapTrace_valid (left right : I → V) (left' right' : J → W) (f : W → V) (g : J → I)
    (hl : ∀ i, left (g i) = f (left' i)) (hr : ∀ i, right (g i) = f (right' i))
    {u v : W} (ds : List (Dart J)) (h : TraceValid left' right' u v ds) :
    TraceValid left right (f u) (f v) (ds.map (mapDart g)) := by
  have htail : ∀ a : Dart J, tail left right (mapDart g a) = f (tail left' right' a) := by
    rintro ⟨i, b⟩; cases b <;> simp [mapDart, tail, hl, hr]
  have hhead : ∀ a : Dart J, head left right (mapDart g a) = f (head left' right' a) := by
    rintro ⟨i, b⟩; cases b <;> simp [mapDart, head, hl, hr]
  induction ds generalizing u with
  | nil => exact congrArg f h
  | cons a ds ih =>
    constructor
    · exact (htail a).trans (congrArg f h.1)
    · rw [hhead]
      exact ih h.2

theorem mapTrace_nonbacktracking (g : J → I) (hg : Function.Injective g)
    (ds : List (Dart J)) (h : TraceNonbacktracking ds) : TraceNonbacktracking (ds.map (mapDart g)) := by
  apply (List.isChain_map (mapDart g)).mpr
  apply h.imp
  intro a b hab heq
  apply hab
  apply mapDart_injective g hg
  exact heq

def Collision.map {left' right' : J → W} (p : Collision left' right')
    (left right : I → V) (f : W → V) (g : J → I) (hg : Function.Injective g)
    (hl : ∀ i, left (g i) = f (left' i)) (hr : ∀ i, right (g i) = f (right' i)) : Collision left right where
  start := f p.start
  finish := f p.finish
  firstTrace := p.firstTrace.map (mapDart g)
  secondTrace := p.secondTrace.map (mapDart g)
  firstValid := mapTrace_valid left right left' right' f g hl hr p.firstTrace p.firstValid
  secondValid := mapTrace_valid left right left' right' f g hl hr p.secondTrace p.secondValid
  firstNonbacktracking := mapTrace_nonbacktracking g hg p.firstTrace p.firstNonbacktracking
  secondNonbacktracking := mapTrace_nonbacktracking g hg p.secondTrace p.secondNonbacktracking
  distinct := fun h => p.distinct ((List.map_injective_iff.mpr (mapDart_injective g hg)) h)

theorem Collision.map_cost {left' right' : J → W} (p : Collision left' right')
    (left right : I → V) (f : W → V) (g : J → I) (hg : Function.Injective g)
    (hl : ∀ i, left (g i) = f (left' i)) (hr : ∀ i, right (g i) = f (right' i)) (w : I → ℝ) :
    (p.map left right f g hg hl hr).cost w = p.cost (w ∘ g) := by
  simp only [Collision.cost, Collision.map, traceCost, List.map_map, Function.comp_def, mapDart]

end OnlineSteinerForest.UpperBound.Girth
