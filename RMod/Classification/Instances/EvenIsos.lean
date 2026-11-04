import RMod.Classification.Abstract.Normalizers
import RMod.Classification.Instances.LinearMonoidal

/-!
# Structural isomorphisms and Mathlib's even category

These adapters preserve both explicitly supplied maps. Mathlib handles
the even Hom subtype and ordinary isomorphism operations; the project
interface retains its separate raw Data and Laws.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification

open CategoryTheory Superfusion.Category

variable (C : WeaklyPointedSuperfusion.{u, v})

noncomputable def IsoData.toEvenIso {X Y : C.data.Obj} (d : IsoData C.data X Y)
    (hd : EvenIsoLaws C.data d) :
    evenObj ℝ (LinearCategory C) X ≅ evenObj ℝ (LinearCategory C) Y where
  hom := ⟨d.hom, hd.hom_even⟩
  inv := ⟨d.inv, hd.inv_even⟩
  hom_inv_id := by apply WideSubcategory.hom_ext; exact hd.hom_inv
  inv_hom_id := by apply WideSubcategory.hom_ext; exact hd.inv_hom

def IsoData.ofEvenIso {X Y : C.data.Obj}
    (e : evenObj ℝ (LinearCategory C) X ≅ evenObj ℝ (LinearCategory C) Y) :
    IsoData C.data X Y := ⟨e.hom.hom, e.inv.hom⟩

theorem evenIsoLaws_ofEvenIso {X Y : C.data.Obj}
    (e : evenObj ℝ (LinearCategory C) X ≅ evenObj ℝ (LinearCategory C) Y) :
    EvenIsoLaws C.data (IsoData.ofEvenIso C e) where
  hom_inv := congrArg (fun f => f.hom) e.hom_inv_id
  inv_hom := congrArg (fun f => f.hom) e.inv_hom_id
  hom_even := e.hom.property
  inv_even := e.inv.property

end RMod.Classification
