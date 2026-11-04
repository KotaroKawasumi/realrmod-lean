import Mathlib.CategoryTheory.Monoidal.Discrete

/-!
# Explicit comparisons between words under a monoidal functor

For a monoidal functor from a discrete monoid, multiply a pair, transport
its product by equality, and expand the new pair with the inverse
tensorator. Three-factor collapse maps keep both parenthesizations
available. These generic Mathlib constructions will control cancellation
of parity contractions independently of the surrounding object strands.
-/

set_option autoImplicit false
universe u v w

namespace RMod.Classification.MonoidalWord

open CategoryTheory MonoidalCategory

variable {G : Type u} [Monoid G] {D : Type v} [Category.{w} D] [MonoidalCategory D]
  (F : Discrete G ⥤ D) [F.Monoidal]

def pairCompare (a b c d : G) (he : a * b = c * d) :
    F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b) ≅
      F.obj (Discrete.mk c) ⊗ F.obj (Discrete.mk d) :=
  Functor.Monoidal.μIso F (Discrete.mk a) (Discrete.mk b) ≪≫
    F.mapIso (Discrete.eqToIso he) ≪≫ (Functor.Monoidal.μIso F (Discrete.mk c) (Discrete.mk d)).symm

def collapseLeft (a b c : G) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk c) ≅
      F.obj (Discrete.mk ((a * b) * c)) :=
  tensorIso (Functor.Monoidal.μIso F (Discrete.mk a) (Discrete.mk b))
    (Iso.refl (F.obj (Discrete.mk c))) ≪≫
      Functor.Monoidal.μIso F (Discrete.mk (a * b)) (Discrete.mk c)

def collapseRight (a b c : G) :
    F.obj (Discrete.mk a) ⊗ (F.obj (Discrete.mk b) ⊗ F.obj (Discrete.mk c)) ≅
      F.obj (Discrete.mk (a * (b * c))) :=
  tensorIso (Iso.refl (F.obj (Discrete.mk a)))
    (Functor.Monoidal.μIso F (Discrete.mk b) (Discrete.mk c)) ≪≫
      Functor.Monoidal.μIso F (Discrete.mk a) (Discrete.mk (b * c))

def tripleCompare (a b c d e f : G) (he : (a * b) * c = (d * e) * f) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk c) ≅
      (F.obj (Discrete.mk d) ⊗ F.obj (Discrete.mk e)) ⊗ F.obj (Discrete.mk f) :=
  collapseLeft F a b c ≪≫ F.mapIso (Discrete.eqToIso he) ≪≫ (collapseLeft F d e f).symm

def replaceLeft (a b c d e : G) (he : a * b = c * d) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk e) ≅
      (F.obj (Discrete.mk c) ⊗ F.obj (Discrete.mk d)) ⊗ F.obj (Discrete.mk e) :=
  tensorIso (pairCompare F a b c d he) (Iso.refl (F.obj (Discrete.mk e)))

def replaceRight (a b c d e : G) (he : b * c = d * e) :
    (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk b)) ⊗ F.obj (Discrete.mk c) ≅
      (F.obj (Discrete.mk a) ⊗ F.obj (Discrete.mk d)) ⊗ F.obj (Discrete.mk e) :=
  α_ (F.obj (Discrete.mk a)) (F.obj (Discrete.mk b)) (F.obj (Discrete.mk c)) ≪≫
    tensorIso (Iso.refl (F.obj (Discrete.mk a))) (pairCompare F b c d e he) ≪≫
      (α_ (F.obj (Discrete.mk a)) (F.obj (Discrete.mk d)) (F.obj (Discrete.mk e))).symm

end RMod.Classification.MonoidalWord
