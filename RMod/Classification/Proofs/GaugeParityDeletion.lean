import RMod.Classification.Instances.GaugeLocalNormalizers
import RMod.Classification.Proofs.RightFactorDeletion
import RMod.Classification.Proofs.ParityContraction
import RMod.Classification.Proofs.GaugeLocalNormalizers
import RMod.Classification.Proofs.ParityPowers

/-!
# Deleting the parity word in a gauge normalizer

The chosen contraction of two odd factors is minus their successive
deletion. This sign must be retained when comparing the specified even
gauge tensorator with homogeneous component comparisons. All equalities
below concern the actual raw maps and include their structural unitors.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

attribute [local implicit_reducible] PiData.shiftObj

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem rightFactorPairNormalizer_deletion (X : C.Obj) (a b : ZMod 2) :
    C.comp (p.rightFactorPairNormalizer X a b).hom (p.rightFactorDeletion X (a + b)).hom =
      C.smul ((-1 : ℝ) ^ (a * b).val)
        (C.comp (p.rightFactorDeletion (C.tensorObj X (p.factor a)) b).hom
          (p.rightFactorDeletion X a).hom) := by
  rcases parity_cases a with rfl | rfl <;> rcases parity_cases b with rfl | rfl
  · change C.comp (C.comp (C.associatorHom X C.tensorUnit C.tensorUnit)
      (C.tensorHom (C.id X) (C.leftUnitorHom C.tensorUnit))) (C.rightUnitorHom X) =
      C.smul 1 (C.comp (C.rightUnitorHom (C.tensorObj X C.tensorUnit)) (C.rightUnitorHom X))
    rw [hC.one_smul, unitors_hom_equal hC, ← rightUnitor_tensor hC]
  · change C.comp (C.comp (C.associatorHom X C.tensorUnit p.object)
      (C.tensorHom (C.id X) (C.leftUnitorHom p.object))) (p.rightZHom X) =
      C.smul 1 (C.comp (p.rightZHom (C.tensorObj X C.tensorUnit)) (C.rightUnitorHom X))
    rw [hC.one_smul]
    change C.comp (C.comp (C.associatorHom X C.tensorUnit p.object)
      (C.whiskerLeft X (C.leftUnitorHom p.object))) (p.rightZHom X) = _
    rw [hC.triangle]
    have he := hp.rightZ_naturality hC (C.rightUnitorHom X) (hC.right_unitor_hom_even X)
    simpa only [ZMod.val_zero, pow_zero, hC.one_smul,
      WeaklyPointedSuperfusionData.whiskerRight] using he
  · change C.comp (C.comp (C.associatorHom X p.object C.tensorUnit)
      (C.tensorHom (C.id X) (C.rightUnitorHom p.object))) (p.rightZHom X) =
      C.smul 1 (C.comp (C.rightUnitorHom (C.tensorObj X p.object)) (p.rightZHom X))
    rw [hC.one_smul, ← rightUnitor_tensor hC]
  · simp only [one_mul, ZMod.val_one, pow_one]
    change C.comp (C.comp (C.associatorHom X p.object p.object)
      (C.tensorHom (C.id X) p.contractionHom)) (C.rightUnitorHom X) =
      C.smul (-1) (C.comp (p.rightZHom (C.tensorObj X p.object)) (p.rightZHom X))
    rw [hp.contraction_eq_z hC, hp.z_self_eq_neg_rightZ hC, hC.smul_comp,
      hC.tensor_smul_right, hC.comp_smul, hC.smul_comp]
    apply congrArg (C.smul (-1))
    have ht := (tensorLeftLaws ⟨C, hC⟩ X).map_comp (p.rightZHom p.object) p.hom
    change C.tensorHom (C.id X) (C.comp (p.rightZHom p.object) p.hom) =
      C.comp (C.tensorHom (C.id X) (p.rightZHom p.object)) (C.tensorHom (C.id X) p.hom) at ht
    rw [ht, ← hC.comp_assoc, ← rightZ_tensor hC, hC.comp_assoc]
    rfl

omit hp in
theorem rightFactorDeletion_tensor (X Y : C.Obj) (a : ZMod 2) :
    (p.rightFactorDeletion (C.tensorObj X Y) a).hom =
      C.comp (C.associatorHom X Y (p.factor a))
        (C.tensorHom (C.id X) (p.rightFactorDeletion Y a).hom) := by
  rcases parity_cases a with rfl | rfl
  · exact rightUnitor_tensor hC X Y
  · exact rightZ_tensor hC X Y

theorem rightFactorMove_deletion (X Y : C.Obj) (a : ZMod 2) :
    C.comp (C.comp (C.comp (C.associatorHom X (p.factor a) Y)
      (C.tensorHom (C.id X) (p.moveFactor a Y).hom))
      (C.associatorInv X Y (p.factor a))) (p.rightFactorDeletion (C.tensorObj X Y) a).hom =
      C.tensorHom (p.rightFactorDeletion X a).hom (C.id Y) := by
  rw [rightFactorDeletion_tensor hC, hC.comp_assoc,
    ← hC.comp_assoc (C.associatorInv X Y (p.factor a)), hC.associator_inv_hom, hC.id_comp,
    hC.comp_assoc]
  have ht := (tensorLeftLaws ⟨C, hC⟩ X).map_comp
    (p.moveFactor a Y).hom (p.rightFactorDeletion Y a).hom
  change C.tensorHom (C.id X) (C.comp (p.moveFactor a Y).hom (p.rightFactorDeletion Y a).hom) =
    C.comp (C.tensorHom (C.id X) (p.moveFactor a Y).hom)
      (C.tensorHom (C.id X) (p.rightFactorDeletion Y a).hom) at ht
  rw [← ht]
  rcases parity_cases a with rfl | rfl
  · change C.comp (C.associatorHom X C.tensorUnit Y)
      (C.tensorHom (C.id X) (C.comp
        (C.comp (C.leftUnitorHom Y) (C.rightUnitorInv Y)) (C.rightUnitorHom Y))) =
      C.tensorHom (C.rightUnitorHom X) (C.id Y)
    rw [hC.comp_assoc, hC.right_unitor_inv_hom, hC.comp_id]
    exact hC.triangle X Y
  · change C.comp (C.associatorHom X p.object Y)
      (C.tensorHom (C.id X) (C.comp (p.centralHom Y) (p.rightZHom Y))) =
      C.tensorHom (p.rightZHom X) (C.id Y)
    rw [hp.central_rightZ hC]
    exact rightZ_middle hC X Y

theorem rightFactorTensorNormalizer_deletion (X Y : C.Obj) (a b : ZMod 2) :
    C.comp (p.rightFactorTensorNormalizer X Y a b).hom
      (p.rightFactorDeletion (C.tensorObj X Y) (a + b)).hom =
      C.smul ((-1 : ℝ) ^ (a * b).val)
        (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom) := by
  let M := C.comp (C.comp (C.associatorHom X (p.factor a) Y)
    (C.tensorHom (C.id X) (p.moveFactor a Y).hom)) (C.associatorInv X Y (p.factor a))
  have hm : C.IsHomogeneous 0 M := comp_even hC
    (comp_even hC (hC.associator_hom_even _ _ _)
      (tensor_even hC (hC.id_even X) (hp.moveFactor_evenIso hC a Y).hom_even))
    (hC.associator_inv_even _ _ _)
  have hM := hp.rightFactorDeletion_naturality hC b M hm
  simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hM
  have hD : C.comp M (p.rightFactorDeletion (C.tensorObj X Y) a).hom =
      C.tensorHom (p.rightFactorDeletion X a).hom (C.id Y) :=
    hp.rightFactorMove_deletion hC X Y a
  have ht {U V W : C.Obj} (f : C.Hom U V) (g : C.Hom V W) :
      C.tensorHom (C.comp f g) (C.id (p.factor b)) =
        C.comp (C.tensorHom f (C.id (p.factor b))) (C.tensorHom g (C.id (p.factor b))) :=
    (tensorRightLaws ⟨C, hC⟩ (p.factor b)).map_comp f g
  have hN : (p.rightFactorTensorNormalizer X Y a b).hom =
      C.comp (C.associatorInv (C.tensorObj X (p.factor a)) Y (p.factor b))
        (C.comp (C.tensorHom M (C.id (p.factor b)))
          (p.rightFactorPairNormalizer (C.tensorObj X Y) a b).hom) := by
    dsimp only [PiData.rightFactorTensorNormalizer, IsoData.trans, IsoData.tensor,
      IsoData.refl, IsoData.symm, IsoData.assoc, M]
    simp only [ht, hC.comp_assoc]
  rw [hN, hC.comp_assoc, hC.comp_assoc, hp.rightFactorPairNormalizer_deletion hC,
    hC.comp_smul, hC.comp_smul]
  apply congrArg (C.smul ((-1 : ℝ) ^ (a * b).val))
  rw [← hC.comp_assoc (C.tensorHom M _), hM, hC.comp_assoc _ M, hD,
    rightFactorDeletion_tensor hC, ← hC.comp_assoc,
    ← hC.comp_assoc (C.associatorInv _ _ _), hC.associator_inv_hom, hC.id_comp,
    interchange_second_even hC _ _ _ _ (hC.id_even Y), hC.id_comp, hC.comp_id]

/-- Deleting the first factor before the second absorbs the pair sign
into signed naturality. This order matches the target gauge comparison. -/
theorem rightFactorPairNormalizer_deletion_tensor (X : C.Obj) (a b : ZMod 2) :
    C.comp (p.rightFactorPairNormalizer X a b).hom (p.rightFactorDeletion X (a + b)).hom =
      C.comp (C.tensorHom (p.rightFactorDeletion X a).hom (C.id (p.factor b)))
        (p.rightFactorDeletion X b).hom := by
  rw [hp.rightFactorPairNormalizer_deletion hC,
    hp.rightFactorDeletion_naturality hC b _
      (hp.rightFactorDeletion_homogeneousIso hC X a).hom_grade, mul_comm b a]

theorem gaugeSourceNormalizer_deletion (X Y : C.Obj) (a b n' : ZMod 2) :
    C.comp (p.gaugeSourceNormalizer X Y a b n').hom
      (p.rightFactorDeletion (C.tensorObj X Y) ((a + b) + n')).hom =
      C.smul ((-1 : ℝ) ^ (a * b + (a + b) * n').val)
        (C.comp (p.rightFactorDeletion
          (C.tensorObj (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))) n').hom
          (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom)) := by
  change C.comp (C.comp (C.tensorHom (p.rightFactorTensorNormalizer X Y a b).hom
    (C.id (p.factor n'))) (p.rightFactorPairNormalizer (C.tensorObj X Y) (a + b) n').hom)
    (p.rightFactorDeletion (C.tensorObj X Y) ((a + b) + n')).hom = _
  have hn := hp.rightFactorDeletion_naturality hC n'
    (p.rightFactorTensorNormalizer X Y a b).hom
    (hp.rightFactorTensorNormalizer_evenIso hC X Y a b).hom_even
  simp only [mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  rw [hC.comp_assoc, hp.rightFactorPairNormalizer_deletion hC, hC.comp_smul,
    ← hC.comp_assoc, hn, hC.comp_assoc, hp.rightFactorTensorNormalizer_deletion hC,
    hC.comp_smul, ← hC.mul_smul, ← parity_power_add, add_comm ((a + b) * n')]

omit hp in
theorem rightFactorDeletion_eq (X : C.Obj) {a b : ZMod 2} (e : a = b) :
    C.comp (IsoData.ofEq C (congrArg (fun q => C.tensorObj X (p.factor q)) e)).hom
      (p.rightFactorDeletion X b).hom = (p.rightFactorDeletion X a).hom := by
  cases e
  exact hC.id_comp _

/-- The local beta scalar is compared with the two homogeneous component
deletions in their actual order. The remaining sign comes entirely from
the source word: the pair of component parities and the tensor parity. -/
theorem gaugeLocalTensorator_deletion_tensor (X Y : C.Obj) (a b n' n c : ZMod 2)
    (e : (a + b) + n' = n + c) (beta : ℝˣ) :
    C.comp (p.gaugeLocalTensorator X Y a b n' n c e beta).hom
      (C.comp (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id (p.factor c)))
        (p.rightFactorDeletion (C.tensorObj X Y) c).hom) =
      C.smul (beta.val * (-1 : ℝ) ^ (a * b + (a + b) * n').val)
        (C.comp (p.rightFactorDeletion
          (C.tensorObj (C.tensorObj X (p.factor a)) (C.tensorObj Y (p.factor b))) n').hom
          (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom)) := by
  have ht : C.comp (p.rightFactorPairNormalizer (C.tensorObj X Y) n c).inv
      (C.comp (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id (p.factor c)))
        (p.rightFactorDeletion (C.tensorObj X Y) c).hom) =
      (p.rightFactorDeletion (C.tensorObj X Y) (n + c)).hom := by
    rw [← hp.rightFactorPairNormalizer_deletion_tensor hC, ← hC.comp_assoc,
      (hp.rightFactorPairNormalizer_evenIso hC _ n c).inv_hom, hC.id_comp]
  change C.comp (C.smul beta.val (C.comp (p.gaugeSourceNormalizer X Y a b n').hom
    (C.comp (IsoData.ofEq C (congrArg (fun q => C.tensorObj (C.tensorObj X Y) (p.factor q)) e)).hom
      (p.rightFactorPairNormalizer (C.tensorObj X Y) n c).inv))) _ = _
  rw [hC.smul_comp, hC.comp_assoc, hC.comp_assoc, ht, rightFactorDeletion_eq hC _ e,
    hp.gaugeSourceNormalizer_deletion hC, ← hC.mul_smul]

/-- Deleting the component shifts before the target tensor factor leaves
only the sign of the two component parities. -/
theorem gaugeLocalTensorator_deletion_inputs (X Y : C.Obj) (a b n' n c : ZMod 2)
    (e : (a + b) + n' = n + c) (beta : ℝˣ) :
    C.comp (p.gaugeLocalTensorator X Y a b n' n c e beta).hom
      (C.comp (C.tensorHom (p.rightFactorDeletion (C.tensorObj X Y) n).hom (C.id (p.factor c)))
        (p.rightFactorDeletion (C.tensorObj X Y) c).hom) =
      C.smul (beta.val * (-1 : ℝ) ^ (a * b).val)
        (C.comp (C.tensorHom
          (C.tensorHom (p.rightFactorDeletion X a).hom (p.rightFactorDeletion Y b).hom)
          (C.id (p.factor n'))) (p.rightFactorDeletion (C.tensorObj X Y) n').hom) := by
  rw [hp.gaugeLocalTensorator_deletion_tensor hC,
    hp.rightFactorDeletion_naturality hC n' _ (hC.tensor_grade _ _
      (hp.rightFactorDeletion_homogeneousIso hC X a).hom_grade
      (hp.rightFactorDeletion_homogeneousIso hC Y b).hom_grade),
    ← hC.mul_smul, parity_power_add, mul_comm n' (a + b), mul_assoc]

end RMod.Classification.PiLaws
