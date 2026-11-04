import RMod.Definitions.WeaklyPointedSuperfusionPredicates

/-!
# Transport of raw Hom operations along object equalities

Dependent extension by zero changes Hom types when its support condition is
resolved. These are equality-elimination lemmas: no categorical laws, new
operations or coherence assumptions are needed.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.HomTransport

variable (D : WeaklyPointedSuperfusionData.{u, v})

theorem id {X X' : D.Obj} (hx : X = X') (e : D.Hom X X = D.Hom X' X') :
    cast e (D.id X) = D.id X' := by
  cases hx
  rfl

theorem comp {X X' Y Y' Z Z' : D.Obj} (hx : X = X') (hy : Y = Y') (hz : Z = Z')
    (e : D.Hom X Y = D.Hom X' Y') (d : D.Hom Y Z = D.Hom Y' Z')
    (c : D.Hom X Z = D.Hom X' Z') (f : D.Hom X Y) (g : D.Hom Y Z) :
    D.comp (cast e f) (cast d g) = cast c (D.comp f g) := by
  cases hx
  cases hy
  cases hz
  rfl

theorem zero {X X' Y Y' : D.Obj} (hx : X = X') (hy : Y = Y')
    (e : D.Hom X Y = D.Hom X' Y') : cast e D.zero = D.zero := by
  cases hx
  cases hy
  rfl

theorem add {X X' Y Y' : D.Obj} (hx : X = X') (hy : Y = Y')
    (e : D.Hom X Y = D.Hom X' Y') (f g : D.Hom X Y) :
    cast e (D.add f g) = D.add (cast e f) (cast e g) := by
  cases hx
  cases hy
  rfl

theorem smul {X X' Y Y' : D.Obj} (hx : X = X') (hy : Y = Y')
    (e : D.Hom X Y = D.Hom X' Y') (r : ℝ) (f : D.Hom X Y) :
    cast e (D.smul r f) = D.smul r (cast e f) := by
  cases hx
  cases hy
  rfl

theorem grade {X X' Y Y' : D.Obj} (hx : X = X') (hy : Y = Y')
    (e : D.Hom X Y = D.Hom X' Y') {a : ZMod 2} (f : D.Hom X Y)
    (hf : D.IsHomogeneous a f) : D.IsHomogeneous a (cast e f) := by
  cases hx
  cases hy
  exact hf

end RMod.Classification.HomTransport
