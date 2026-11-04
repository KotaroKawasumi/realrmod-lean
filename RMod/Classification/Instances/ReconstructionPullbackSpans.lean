import RMod.Classification.Instances.ReconstructionTwistData
import RMod.Classification.Instances.PullbackLinearCategory
import RMod.Classification.Proofs.ReferenceComponentSpan
import Mathlib.CategoryTheory.Pi.Basic

/-!
# The pullback carrier as the product of the chosen reference spans

The two descriptions retain the same objects and all the same morphisms
in every group coordinate. Component membership and span membership are
identified by the proved reference theorem. Mathlib supplies the ordinary
functors and equivalence, whose unit and counit maps are identities.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable (A C : PiSuperfusion.{0, 0}) (hC : ReferenceProperty C.data)

noncomputable def reconstructionPullbackSpanFunctor :
    PullbackCategory C.data hC (reconstructionTwistData A C hC) ⥤
      ((g : SimpleOrbit A.toWeaklyPointedSuperfusion) →
        HomogeneousSpanCategory C.toWeaklyPointedSuperfusion
          (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) where
  obj X g := ⟨(X g).val, (reference_component_iff_span C hC (simpleOrbitType A g) (X g).val).mp (X g).property⟩
  map f g := ObjectProperty.homMk (f g)
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def reconstructionSpanPullbackFunctor :
    ((g : SimpleOrbit A.toWeaklyPointedSuperfusion) →
        HomogeneousSpanCategory C.toWeaklyPointedSuperfusion
          (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) ⥤
      PullbackCategory C.data hC (reconstructionTwistData A C hC) where
  obj X g := ⟨(X g).obj, (reference_component_iff_span C hC (simpleOrbitType A g) (X g).obj).mpr (X g).property⟩
  map f g := (f g).hom
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def reconstructionPullbackSpanEquivalence :
    PullbackCategory C.data hC (reconstructionTwistData A C hC) ≌
      ((g : SimpleOrbit A.toWeaklyPointedSuperfusion) →
        HomogeneousSpanCategory C.toWeaklyPointedSuperfusion
          (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) where
  functor := reconstructionPullbackSpanFunctor A C hC
  inverse := reconstructionSpanPullbackFunctor A C hC
  unitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun f => by
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    exact (Category.comp_id f).trans (Category.id_comp f).symm)
  counitIso := NatIso.ofComponents (fun X => Iso.refl X) (fun f => by
    change f ≫ 𝟙 _ = 𝟙 _ ≫ f
    exact (Category.comp_id f).trans (Category.id_comp f).symm)

  functor_unitIso_comp X := by
    change (reconstructionPullbackSpanFunctor A C hC).map (𝟙 X) ≫ 𝟙 _ = 𝟙 _
    rw [(reconstructionPullbackSpanFunctor A C hC).map_id, Category.id_comp]

/-- Mathlib's product equivalence retains every selected component inverse. -/
noncomputable def reconstructionComponentFamilyEquivalence :
    ((g : SimpleOrbit A.toWeaklyPointedSuperfusion) →
        HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
          (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object) ≌
      ((g : SimpleOrbit A.toWeaklyPointedSuperfusion) →
        HomogeneousSpanCategory C.toWeaklyPointedSuperfusion
          (referenceSimpleRepresentative C hC (simpleOrbitType A g)).data.object) :=
  Equivalence.pi (fun g => ((reconstructionComponentSystem A C hC).component g).data)

noncomputable def reconstructionPullbackFamilyEquivalence :
    PullbackCategory C.data hC (reconstructionTwistData A C hC) ≌
      ((g : SimpleOrbit A.toWeaklyPointedSuperfusion) →
        HomogeneousSpanCategory A.toWeaklyPointedSuperfusion
          (simpleOrbitRepresentative A.toWeaklyPointedSuperfusion g).data.object) :=
  (reconstructionPullbackSpanEquivalence A C hC).trans (reconstructionComponentFamilyEquivalence A C hC).symm

end RMod.Classification
