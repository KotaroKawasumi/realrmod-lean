import RMod.Classification.Instances.SpanFamilyPreimages
import Mathlib.CategoryTheory.Equivalence

/-!
# The actual inverse to a family realization from its even preimages

Lift each conjugated target morphism through full faithfulness. The unit
is the lift of the inverse counit. Naturality and the triangle follow
from these lifts, so Mathlib's ordinary equivalence retains the chosen
even counit maps and does not make another choice of object isomorphisms.
-/

set_option autoImplicit false

namespace RMod.Classification.SpanFamilyPreimages

open CategoryTheory

variable {C : WeaklyPointedSuperfusion.{0, 0}} {I : Type} {S : I → C.data.Obj}
  {F : SpanFamilyCategory C S ⥤ LinearCategory C} (p : SpanFamilyPreimages C S F) (hF : F.FullyFaithful)

def inverseFunctor : LinearCategory C ⥤ SpanFamilyCategory C S where
  obj := p.data.family
  map {X Y} f := hF.preimage ((p.counitIso X).hom ≫ f ≫ (p.counitIso Y).inv)
  map_id X := by apply hF.map_injective; simp
  map_comp f g := by apply hF.map_injective; simp

def inverseUnitIso : 𝟭 (SpanFamilyCategory C S) ≅ F ⋙ p.inverseFunctor hF :=
  NatIso.ofComponents (fun X => (hF.preimageIso (p.counitIso (F.obj X))).symm)
    (by
      intro X Y f
      apply hF.map_injective
      change F.map (f ≫ hF.preimage (p.counitIso (F.obj Y)).inv) =
        F.map (hF.preimage (p.counitIso (F.obj X)).inv ≫
          hF.preimage ((p.counitIso (F.obj X)).hom ≫ F.map f ≫
            (p.counitIso (F.obj Y)).inv))
      simp only [CategoryTheory.Functor.map_comp, hF.map_preimage, Iso.inv_hom_id_assoc])

def inverseCounitIso : p.inverseFunctor hF ⋙ F ≅ 𝟭 (LinearCategory C) :=
  NatIso.ofComponents p.counitIso (by
    intro X Y f
    change F.map (hF.preimage ((p.counitIso X).hom ≫ f ≫ (p.counitIso Y).inv)) ≫
      (p.counitIso Y).hom = (p.counitIso X).hom ≫ f
    rw [hF.map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])

def underlyingEquivalence : SpanFamilyCategory C S ≌ LinearCategory C where
  functor := F
  inverse := p.inverseFunctor hF
  unitIso := p.inverseUnitIso hF
  counitIso := p.inverseCounitIso hF
  functor_unitIso_comp X := by
    change F.map (hF.preimage (p.counitIso (F.obj X)).inv) ≫
      (p.counitIso (F.obj X)).hom = _
    rw [hF.map_preimage]
    exact (p.counitIso (F.obj X)).inv_hom_id

end RMod.Classification.SpanFamilyPreimages
