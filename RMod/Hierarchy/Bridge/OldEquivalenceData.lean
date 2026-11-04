import RMod.Hierarchy.Abstract.Equivalence
import RMod.Hierarchy.Bridge.Superfunctors
import RMod.Hierarchy.Bridge.EvenMonoidalEquivalence
import RMod.Classification.Instances.MonoidalFunctors

/-!
# Data of transported monoidal superequivalences

The enriched maps are restrictions of the old graded linear functors.
Every even comparison isomorphism is reflected through the fully faithful
even-category adapter, keeping its specified hom and inverse.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

def ofOldEvenIso (C : WeaklyPointedSuperfusion.{0, 0}) {X Y : C.data.Obj}
    (f : C.data.Hom X Y) (g : C.data.Hom Y X)
    (hf : C.data.IsHomogeneous 0 f) (hg : C.data.IsHomogeneous 0 g)
    (hfg : C.data.comp f g = C.data.id X) (hgf : C.data.comp g f = C.data.id Y) :
    evenObj (ofOldSupercategory C) X ≅ evenObj (ofOldSupercategory C) Y :=
  (evenForget C).preimageIso {
    hom := ⟨f, hf⟩
    inv := ⟨g, hg⟩
    hom_inv_id := WideSubcategory.hom_ext _ hfg
    inv_hom_id := WideSubcategory.hom_ext _ hgf }

theorem ofOldEvenIso_hom (C : WeaklyPointedSuperfusion.{0, 0}) {X Y : C.data.Obj}
    (f : C.data.Hom X Y) (g : C.data.Hom Y X)
    (hf : C.data.IsHomogeneous 0 f) (hg : C.data.IsHomogeneous 0 g)
    (hfg : C.data.comp f g = C.data.id X) (hgf : C.data.comp g f = C.data.id Y) :
    (evenHomEquiv C X Y (ofOldEvenIso C f g hf hg hfg hgf).hom).hom = f := by
  exact congrArg (fun h : oldEvenObj C X ⟶ oldEvenObj C Y => h.hom)
    ((evenForget C).map_preimage ⟨f, hf⟩)

variable {C D : WeaklyPointedSuperfusion.{0, 0}} (E : Classification.MonoidalSuperequivalence C D)

def ofOldEquivalenceForward : Classification.Superfunctor C D :=
  ⟨E.data.forward.toPrefunctor, E.laws.forward.toSuperfunctorLaws⟩
def ofOldEquivalenceBackward : Classification.Superfunctor D C :=
  ⟨E.data.backward, E.laws.backward⟩

def ofOldMonoidalSuperequivalenceData :
    MonoidalSuperequivalenceData (ofOldMonoidalSupercategory C) (ofOldMonoidalSupercategory D) where
  forward := ofOldSuperfunctorData (ofOldEquivalenceForward E)
  backward := ofOldSuperfunctorData (ofOldEquivalenceBackward E)
  tensorIso X Y := ofOldEvenIso D (E.data.forward.tensorHom X Y) (E.data.forward.tensorInv X Y)
    (E.laws.forward.tensor_hom_even X Y) (E.laws.forward.tensor_inv_even X Y)
    (E.laws.forward.tensor_hom_inv X Y) (E.laws.forward.tensor_inv_hom X Y)
  unitIso := ofOldEvenIso D E.data.forward.unitHom E.data.forward.unitInv
    E.laws.forward.unit_hom_even E.laws.forward.unit_inv_even
    E.laws.forward.unit_hom_inv E.laws.forward.unit_inv_hom
  unit X := ofOldEvenIso C (E.data.unitHom X) (E.data.unitInv X)
    (E.laws.unit_hom_even X) (E.laws.unit_inv_even X)
    (E.laws.unit_hom_inv X) (E.laws.unit_inv_hom X)
  counit Y := ofOldEvenIso D (E.data.counitHom Y) (E.data.counitInv Y)
    (E.laws.counit_hom_even Y) (E.laws.counit_inv_even Y)
    (E.laws.counit_hom_inv Y) (E.laws.counit_inv_hom Y)

end RMod.Legacy.Hierarchy
