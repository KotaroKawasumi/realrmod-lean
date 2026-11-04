import RMod.Classification.Abstract.Equivalence

/-!
# Identity and composition data

Functor maps use Mathlib's prefunctor operations. The composite tensorator
first uses the outer tensorator and then the image of the inner one; its
inverse follows the reverse route. All maps here depend only on data.
-/

set_option autoImplicit false
universe u₁ v₁ u₂ v₂ u₃ v₃

namespace RMod.Classification

variable {A : WeaklyPointedSuperfusionData.{u₁, v₁}}
  {B : WeaklyPointedSuperfusionData.{u₂, v₂}}
  {C : WeaklyPointedSuperfusionData.{u₃, v₃}}

def MonoidalSuperfunctorData.identity (A : WeaklyPointedSuperfusionData.{u₁, v₁}) :
    MonoidalSuperfunctorData A A where
  toPrefunctor := Prefunctor.id A.Obj
  tensorHom X Y := A.id (A.tensorObj X Y)
  tensorInv X Y := A.id (A.tensorObj X Y)
  unitHom := A.id A.tensorUnit
  unitInv := A.id A.tensorUnit

def MonoidalSuperfunctorData.compose (F : MonoidalSuperfunctorData A B)
    (G : MonoidalSuperfunctorData B C) : MonoidalSuperfunctorData A C where
  toPrefunctor := F.toPrefunctor.comp G.toPrefunctor
  tensorHom X Y := C.comp (G.tensorHom (F.obj X) (F.obj Y)) (G.map (F.tensorHom X Y))
  tensorInv X Y := C.comp (G.map (F.tensorInv X Y)) (G.tensorInv (F.obj X) (F.obj Y))
  unitHom := C.comp G.unitHom (G.map F.unitHom)
  unitInv := C.comp (G.map F.unitInv) G.unitInv

/-- Composition also retains explicit unit and counit inverses. -/
def MonoidalSuperequivalenceData.compose (E : MonoidalSuperequivalenceData A B)
    (F : MonoidalSuperequivalenceData B C) : MonoidalSuperequivalenceData A C where
  forward := E.forward.compose F.forward
  backward := F.backward.comp E.backward
  unitHom X := A.comp (E.unitHom X) (E.backward.map (F.unitHom (E.forward.obj X)))
  unitInv X := A.comp (E.backward.map (F.unitInv (E.forward.obj X))) (E.unitInv X)
  counitHom Y := C.comp (F.forward.map (E.counitHom (F.backward.obj Y))) (F.counitHom Y)
  counitInv Y := C.comp (F.counitInv Y) (F.forward.map (E.counitInv (F.backward.obj Y)))

def MonoidalSuperequivalenceData.identity (A : WeaklyPointedSuperfusionData.{u₁, v₁}) :
    MonoidalSuperequivalenceData A A where
  forward := MonoidalSuperfunctorData.identity A
  backward := Prefunctor.id A.Obj
  unitHom := A.id
  unitInv := A.id
  counitHom := A.id
  counitInv := A.id

end RMod.Classification
