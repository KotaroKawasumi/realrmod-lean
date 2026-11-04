import RMod.BrundanEllis.StackingHullSuperMonoidal
import RMod.BrundanEllis.StackingHullOrbits
import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence

/-! Fusion structure on a completion closed under the ambient tensor and
duals. Parity closure, finite semisimplicity and finite simple orbits have
already been proved from the definition of the hull. The two dual-closure
conditions are exposed for subsequent verification on the diagonal family. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  preservesBinaryBiproducts_of_preservesBiproducts
namespace RMod.BrundanEllis
variable (C : WeaklyPointedFusionPiSuperCat) {I : Type} (Z : I → Even C)
  [ObjectProperty.IsMonoidal (AddPiHull C Z)]

/-- The parity object belongs to every unital completion. -/
theorem hull_pi_mem : AddPiHull C Z (evenObj C (MonoidalPiSuperCategory.pi (C := C))) :=
  (AddPiHull.iso_iff (ρ_ (evenObj C (MonoidalPiSuperCategory.pi (C := C))))).mp
    (AddPiHull.parity (ObjectProperty.prop_unit (AddPiHull C Z)))

instance hullPi : MonoidalPiSuperCategory (HullCategory C Z) where
  pi := ⟨evenObj C (MonoidalPiSuperCategory.pi (C := C)), hull_pi_mem C Z⟩
  hom := MonoidalPiSuperCategory.hom (C := C)
  inv := MonoidalPiSuperCategory.inv (C := C)
  hom_inv := MonoidalPiSuperCategory.hom_inv (C := C)
  inv_hom := MonoidalPiSuperCategory.inv_hom (C := C)

/-- Selected ambient duals, with their actual evaluation and coevaluation
transported by the fully faithful monoidal inclusion. -/
@[implicit_reducible] def hullRigid
    (hL : ∀ X : Even (HullCategory C Z), AddPiHull C Z (ᘁX.obj))
    (hR : ∀ X : Even (HullCategory C Z), AddPiHull C Z (X.objᘁ)) :
    RigidCategory (Even (HullCategory C Z)) := by
  let F := (hullInclusion C Z).forget
  letI : F.Monoidal := (hullInclusionMonoidal C Z).toMonoidal
  exact {
    leftDual X := {
      leftDual := evenObj _ ⟨ᘁX.obj, hL X⟩
      exact := by
        letI : ExactPairing (F.obj (evenObj _ ⟨ᘁX.obj, hL X⟩)) (F.obj X) := by
          change ExactPairing (ᘁX.obj) X.obj
          infer_instance
        exact ExactPairing.ofFullyFaithful F _ _ }
    rightDual X := {
      rightDual := evenObj _ ⟨X.objᘁ, hR X⟩
      exact := by
        letI : ExactPairing (F.obj X) (F.obj (evenObj _ ⟨X.objᘁ, hR X⟩)) := by
          change ExactPairing X.obj (X.objᘁ)
          infer_instance
        exact ExactPairing.ofFullyFaithful F _ _ } }

variable
  (hL : ∀ X : Even (HullCategory C Z), AddPiHull C Z (ᘁX.obj))
  (hR : ∀ X : Even (HullCategory C Z), AddPiHull C Z (X.objᘁ))

/-- All the fusion finiteness and semisimplicity conditions are inherited. -/
@[implicit_reducible] def hullFusion :
    letI := hullRigid C Z hL hR
    FusionPiSuperCategory (HullCategory C Z) := by
  letI := hullRigid C Z hL hR
  exact {
    hom_finite X Y a := FusionPiSuperCategory.hom_finite (C := C) X.obj Y.obj a
    semisimple := hull_semisimple C Z
    finite_simples := hull_finite_simples C Z
    simple_unit := hull_simple_of_ambient C Z _ (FusionPiSuperCategory.simple_unit (C := C)) }

/-- The split-unit algebra is literally the same total endomorphism algebra. -/
theorem hull_splitUnit : IsSplitUnit (HullCategory C Z) :=
  WeaklyPointedFusionPiSuperCategory.splitUnit (C := C)

/-- Weak invertibility descends along the fully faithful inclusion and its
finite-biproduct comparisons. The chosen right dual is the ambient one. -/
theorem hull_weaklyPointed :
    letI := hullRigid C Z hL hR
    IsWeaklyPointed (HullCategory C Z) := by
  letI := hullRigid C Z hL hR
  intro X hX
  letI := hX
  have hs : Simple X.obj := hull_simple_ambient C Z X
  obtain ⟨p, q, ⟨e⟩⟩ := WeaklyPointedFusionPiSuperCategory.weaklyPointed (C := C) X.obj hs
  let F := (hullInclusion C Z).forget
  let U : Fin p → Even (HullCategory C Z) := fun _ => 𝟙_ _
  let P : Fin q → Even (HullCategory C Z) :=
    fun _ => evenObj _ (MonoidalPiSuperCategory.pi (C := HullCategory C Z))
  refine ⟨p, q, ⟨F.preimageIso ?_⟩⟩
  exact e ≪≫ (biprod.mapIso (F.mapBiproduct U).symm (F.mapBiproduct P).symm) ≪≫
    (F.mapBiprod (⨁ U) (⨁ P)).symm

/-- Package the proved restricted structures. This is an auxiliary construction,
not a substitute for proving closure of a specific diagonal family. -/
def hullFusionCategory : WeaklyPointedFusionPiSuperCat := by
  letI := hullRigid C Z hL hR
  letI := hullFusion C Z hL hR
  letI : WeaklyPointedFusionPiSuperCategory (HullCategory C Z) := {
    splitUnit := hull_splitUnit C Z
    weaklyPointed := hull_weaklyPointed C Z hL hR }
  exact { carrier := HullCategory C Z }

end RMod.BrundanEllis
