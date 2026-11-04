import RMod.BrundanEllis.StackingKaroubiEvenRigid
import RMod.BrundanEllis.StackingKaroubiEmbeddingMonoidal

/-! On an identity corner the chosen dual projector is the identity.
This gives the explicit comparison between the completed right dual and
the embedding of the original right dual. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Idempotents
namespace RMod.BrundanEllis.Stacking.KaroubiSuper
variable (C : Type) [SuperCategory C] [MonoidalCategory (Even C)] [RigidCategory (Even C)]

def embeddingDualIso (X : Even C) :
    ((embedding C).forget.obj X)ᘁ ≅ (embedding C).forget.obj (Xᘁ) := by
  apply (evenEquivalence (C := C)).functor.preimageIso
  apply eqToIso
  change KaroubiTensor.rightDualObject ((toKaroubi (Even C)).obj X) =
    (toKaroubi (Even C)).obj (Xᘁ)
  unfold KaroubiTensor.rightDualObject
  simp only [toKaroubi, Karoubi.coe_p, rightAdjointMate_id]

def embeddingSelfDualIso (X : Even C) :
    (embedding C).forget.obj X ⊗ ((embedding C).forget.obj X)ᘁ ≅
      (embedding C).forget.obj (X ⊗ Xᘁ) :=
  (Iso.refl _ ⊗ᵢ embeddingDualIso C X) ≪≫ (embeddingMonoidal C).μIso X (Xᘁ)

end RMod.BrundanEllis.Stacking.KaroubiSuper
