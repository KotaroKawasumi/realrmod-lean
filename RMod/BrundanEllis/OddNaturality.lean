import RMod.BrundanEllis.Foundation
import RMod.Statement.EnrichmentBridge
import RMod.Hierarchy.Instances.HomogeneousOperations
import RMod.Hierarchy.Instances.HomogeneousBasis
import RMod.Hierarchy.Instances.GradedTensorPoints

/-! Homogeneous vectors detect odd supernatural transformations.
This is specialized to real super vector spaces: the basis of the odd line
reduces Mathlib's Hom-object equation to the usual signed naturality equation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open CategoryTheory CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
open scoped TensorProduct
namespace RMod.BrundanEllis

/-- A local use of the established total-composition lemmas on the same enrichment. -/
abbrev homogeneousCategory (C : Type) [SuperCategory C] : RMod.Legacy.Supercategory :=
  RMod.StatementLegacy.toLegacySupercategory (EnrichedCat.of SuperVec C)

/-- Signed naturality on homogeneous inputs gives full enriched odd naturality. -/
theorem odd_naturality_of_homogeneous
    {C D : Type} [SuperCategory C] [SuperCategory D]
    (F G : SuperFunctor C D) (α : ∀ X, oddLine ⟶ SHom D (F.obj X) (G.obj X))
    (h : ∀ (X Y : C) (a : ZMod 2) (f : SHom C X Y a),
      tComp D (homogeneousPoint 1 (α X)) (fun b => G.map X Y b ((Pi.single a f : THom C X Y) b)) =
        (-1 : ℝ) ^ a.val •
          tComp D (fun b => F.map X Y b ((Pi.single a f : THom C X Y) b)) (homogeneousPoint 1 (α Y)))
    (X Y : C) :
    koszulMap oddLine (SHom C X Y) ≫ (F.map X Y ⊗ₘ α Y) ≫
      eComp SuperVec (F.obj X) (F.obj Y) (G.obj Y) =
    (α X ⊗ₘ G.map X Y) ≫ eComp SuperVec (F.obj X) (G.obj X) (G.obj Y) := by
  funext n
  apply tensorObj_ext
  intro i j hij
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro f g
  by_cases hi : i = 1
  · subst i
    rw [RMod.Legacy.homogeneousLine_smul_basis 1 f]
    erw [← TensorProduct.smul_tmul']
    simp only [map_smul]
    congr 1
    let b := (GradedObject.singleObjApplyIso (1 : ZMod 2) (ModuleCat.of ℝ ℝ)).inv 1
    change eComp SuperVec (F.obj X) (F.obj Y) (G.obj Y) n
      ((F.map X Y ⊗ₘ α Y) n
        (RMod.Legacy.koszulMap oddLine (SHom C X Y) n
          (RMod.Legacy.gradedTmul oddLine (SHom C X Y) 1 j n hij b g))) =
      eComp SuperVec (F.obj X) (G.obj X) (G.obj Y) n
        ((α X ⊗ₘ G.map X Y) n
          (RMod.Legacy.gradedTmul oddLine (SHom C X Y) 1 j n hij b g))
    erw [RMod.Legacy.koszulMap_gradedTmul oddLine (SHom C X Y) 1 j n hij b g,
      map_smul, map_smul, RMod.Legacy.tensorHom_gradedTmul,
      RMod.Legacy.tensorHom_gradedTmul]
    have ha : homogeneousPoint 1 (α X) ∈
        RMod.Legacy.grade (homogeneousCategory D) (F.obj X) (G.obj X) 1 := by
      intro k hk
      change homogeneousPoint 1 (α X) k = 0
      simp only [homogeneousPoint, dif_neg hk]
    have hf : (fun k => F.map X Y k ((Pi.single j g : THom C X Y) k)) ∈
        RMod.Legacy.grade (homogeneousCategory D) (F.obj X) (F.obj Y) j := by
      intro k hk
      simp only [Pi.single_eq_of_ne hk, map_zero]
    have he := congrFun (h X Y j g) n
    change RMod.Legacy.tComp (homogeneousCategory D).data
        (homogeneousPoint 1 (α X))
        (fun k => G.map X Y k ((Pi.single j g : THom C X Y) k)) n =
      (-1 : ℝ) ^ j.val • RMod.Legacy.tComp (homogeneousCategory D).data
        (fun k => F.map X Y k ((Pi.single j g : THom C X Y) k))
        (homogeneousPoint 1 (α Y)) n at he
    rw [RMod.Legacy.tComp_homogeneous_at (homogeneousCategory D) 1 j n hij _ _ ha,
      RMod.Legacy.tComp_homogeneous_at (homogeneousCategory D) j 1 n
        ((add_comm j 1).trans hij) _ _ hf] at he
    simp only [one_mul, Pi.single_eq_same] at he ⊢
    exact he.symm
  · haveI : Subsingleton (oddLine i) := RMod.Legacy.homogeneousLine_subsingleton 1 i hi
    rw [Subsingleton.elim f 0]
    simp only [TensorProduct.zero_tmul, map_zero]

end RMod.BrundanEllis
