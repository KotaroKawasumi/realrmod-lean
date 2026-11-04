import RMod.Classification.Proofs.GaugeParityDeletion

/-!
# Normalizers compared with ordered homogeneous deletions

Delete the inner parity factor before the outer one. In this order the
pair contraction sign is already accounted for by signed naturality.
The left and right normalizers therefore reduce to their respective
ordered deletions, with the ordinary associator retained on the left.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem normalRight_deletion (X Y Z : C.Obj) (a b : ZMod 2) :
    C.comp (p.normalRight X Y Z a b).hom
      (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) (a + b)).hom =
      C.comp (C.tensorHom (C.tensorHom (C.id X)
        (p.rightFactorDeletion (C.tensorObj Y Z) a).hom) (C.id (p.factor b)))
        (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) b).hom := by
  have ht {U V W : C.Obj} (f : C.Hom U V) (g : C.Hom V W) :
      C.tensorHom (C.comp f g) (C.id (p.factor b)) =
        C.comp (C.tensorHom f (C.id (p.factor b))) (C.tensorHom g (C.id (p.factor b))) :=
    (tensorRightLaws ⟨C, hC⟩ (p.factor b)).map_comp f g
  have hd : C.comp (C.associatorInv X (C.tensorObj Y Z) (p.factor a))
      (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) a).hom =
      C.tensorHom (C.id X) (p.rightFactorDeletion (C.tensorObj Y Z) a).hom := by
    rw [rightFactorDeletion_tensor hC, ← hC.comp_assoc, hC.associator_inv_hom, hC.id_comp]
  change C.comp (C.comp (C.comp
    (C.tensorHom (C.associatorInv X (C.tensorObj Y Z) (p.factor a)) (C.id (p.factor b)))
    (C.associatorHom (C.tensorObj X (C.tensorObj Y Z)) (p.factor a) (p.factor b)))
    (C.tensorHom (C.id (C.tensorObj X (C.tensorObj Y Z))) (p.multiplyFactors a b).hom)) _ = _
  rw [hC.comp_assoc (C.tensorHom _ _)]
  change C.comp (C.comp
    (C.tensorHom (C.associatorInv X (C.tensorObj Y Z) (p.factor a)) (C.id (p.factor b)))
    (p.rightFactorPairNormalizer (C.tensorObj X (C.tensorObj Y Z)) a b).hom) _ = _
  rw [hC.comp_assoc, hp.rightFactorPairNormalizer_deletion_tensor hC,
    ← hC.comp_assoc, ← ht, hd]

theorem normalLeft_deletion (X Y Z : C.Obj) (a b : ZMod 2) :
    C.comp (p.normalLeft X Y Z a b).hom
      (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) (a + b)).hom =
      C.comp (C.tensorHom (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) a).hom
        (C.id Z)) (C.id (p.factor b)))
        (C.comp (p.rightFactorDeletion (C.tensorObj (C.tensorObj X Y) Z) b).hom
          (C.associatorHom X Y Z)) := by
  let M := C.comp (C.comp (C.associatorHom (C.tensorObj X Y) (p.factor a) Z)
    (C.tensorHom (C.id (C.tensorObj X Y)) (p.moveFactor a Z).hom))
    (C.associatorInv (C.tensorObj X Y) Z (p.factor a))
  let N := C.comp M (C.tensorHom (C.associatorHom X Y Z) (C.id (p.factor a)))
  have ht {U V W : C.Obj} (f : C.Hom U V) (g : C.Hom V W) :
      C.tensorHom (C.comp f g) (C.id (p.factor b)) =
        C.comp (C.tensorHom f (C.id (p.factor b))) (C.tensorHom g (C.id (p.factor b))) :=
    (tensorRightLaws ⟨C, hC⟩ (p.factor b)).map_comp f g
  have hN : C.comp N (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) a).hom =
      C.comp (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) a).hom (C.id Z))
        (C.associatorHom X Y Z) := by
    have hn := hp.rightFactorDeletion_naturality hC a (C.associatorHom X Y Z)
      (hC.associator_hom_even X Y Z)
    simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
    change C.comp (C.comp M _) _ = _
    rw [hC.comp_assoc, hn, ← hC.comp_assoc, hp.rightFactorMove_deletion hC]
  have hL : (p.normalLeft X Y Z a b).hom =
      C.comp (C.tensorHom N (C.id (p.factor b)))
        (p.rightFactorPairNormalizer (C.tensorObj X (C.tensorObj Y Z)) a b).hom := by
    dsimp only [PiData.normalLeft, PiData.rightFactorPairNormalizer, IsoData.trans,
      IsoData.tensor, IsoData.refl, IsoData.assoc, IsoData.symm, N, M]
    simp only [ht, hC.comp_assoc]
  have hn := hp.rightFactorDeletion_naturality hC b (C.associatorHom X Y Z)
    (hC.associator_hom_even X Y Z)
  simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  rw [hL, hC.comp_assoc, hp.rightFactorPairNormalizer_deletion_tensor hC,
    ← hC.comp_assoc, ← ht, hN, ht, hC.comp_assoc, hn]

/-- The specified weighted associator intertwines the two ordered
deletions with exactly its omega scalar. No normalizer is replaced. -/
theorem localAssociator_deletion (X Y Z : C.Obj) (a b c d : ZMod 2)
    (e : a + b = c + d) (omega : ℝˣ) :
    C.comp (p.localAssociator X Y Z a b c d e omega).hom
      (C.comp (C.tensorHom (C.tensorHom (C.id X)
        (p.rightFactorDeletion (C.tensorObj Y Z) c).hom) (C.id (p.factor d)))
        (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) d).hom) =
      C.smul omega.val
        (C.comp (C.tensorHom (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) a).hom
          (C.id Z)) (C.id (p.factor b)))
          (C.comp (p.rightFactorDeletion (C.tensorObj (C.tensorObj X Y) Z) b).hom
            (C.associatorHom X Y Z))) := by
  have hr : C.comp (p.normalRight X Y Z c d).inv
      (C.comp (C.tensorHom (C.tensorHom (C.id X)
        (p.rightFactorDeletion (C.tensorObj Y Z) c).hom) (C.id (p.factor d)))
        (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) d).hom) =
      (p.rightFactorDeletion (C.tensorObj X (C.tensorObj Y Z)) (c + d)).hom := by
    rw [← hp.normalRight_deletion hC, ← hC.comp_assoc,
      (hp.normalRight_evenIso hC X Y Z c d).inv_hom, hC.id_comp]
  change C.comp (C.smul omega.val (C.comp (p.normalLeft X Y Z a b).hom
    (C.comp (IsoData.ofEq C (congrArg (fun q => C.tensorObj
      (C.tensorObj X (C.tensorObj Y Z)) (p.factor q)) e)).hom (p.normalRight X Y Z c d).inv))) _ = _
  rw [hC.smul_comp, hC.comp_assoc, hC.comp_assoc, hr, rightFactorDeletion_eq hC _ e,
    hp.normalLeft_deletion hC]

end RMod.Classification.PiLaws
