import RMod.Classification.Instances.EquivalenceIndexedComparisons
import RMod.Classification.Proofs.ConvolutionIndexedComparisons

/-!
# Factoring the given inverse tensorators out of triple evaluation

Naturality of the target binary evaluation moves an even inverse
tensorator past the outer comparison. Each nested comparison becomes
the corresponding inverse-tensorator route followed by ordinary target
triple evaluation. No associativity hypothesis is substituted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (s t : Twist)
  (E : MonoidalSuperequivalence (twistedPullback C hC s).toWeaklyPointedSuperfusion
    (twistedPullback C hC t).toWeaklyPointedSuperfusion)

theorem equivalenceIndexedLeftComparison_factorization (X Y Z : PullbackObj C s.data)
    (g h k u w : t.data.group) (eu : g * h = u) (ew : u * k = w) :
    (equivalenceIndexedLeftComparisonData C hC s t E X Y Z g h k u w eu ew).hom =
      C.comp (E.data.forward.tensorInv ((twistedPullback C hC s).data.tensorObj X Y) Z w)
        (C.comp (convolutionHom C hC t.data (E.data.forward.tensorInv X Y)
          (fun j => C.id (E.data.forward.obj Z j).val) w)
          (convolutionIndexedLeftComparisonData C hC t.data
            (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z) g h k u w eu ew).hom) := by
  have hn := convolutionIndexedComparison_naturality C hC t.data
    (E.data.forward.tensorInv X Y) (fun j => C.id (E.data.forward.obj Z j).val)
    (E.laws.forward.tensor_inv_even X Y) (fun j => hC.id_even (E.data.forward.obj Z j).val) u k w ew
  simp only [zero_add, mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  have ht {P Q R : C.Obj} (f : C.Hom P Q) (q : C.Hom Q R) :
      C.tensorHom (C.comp f q) (C.id (E.data.forward.obj Z k).val) =
        C.comp (C.tensorHom f (C.id (E.data.forward.obj Z k).val))
          (C.tensorHom q (C.id (E.data.forward.obj Z k).val)) :=
    (tensorRightLaws ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (E.data.forward.obj Z k).val).map_comp f q
  dsimp only [equivalenceIndexedLeftComparisonData, equivalenceIndexedComparisonData,
    equivalenceTensoratorComponentData, convolutionIndexedLeftComparisonData,
    IsoData.trans, IsoData.tensor, IsoData.refl]
  rw [ht]
  simp only [hC.comp_assoc]
  apply congrArg (C.comp _)
  rw [← hC.comp_assoc]
  exact (congrArg (fun z => C.comp z _) hn.symm).trans (hC.comp_assoc _ _ _)

theorem equivalenceIndexedRightComparison_factorization (X Y Z : PullbackObj C s.data)
    (g h k v w : t.data.group) (ev : h * k = v) (ew : g * v = w) :
    (equivalenceIndexedRightComparisonData C hC s t E X Y Z g h k v w ev ew).hom =
      C.comp (E.data.forward.tensorInv X ((twistedPullback C hC s).data.tensorObj Y Z) w)
        (C.comp (convolutionHom C hC t.data (fun j => C.id (E.data.forward.obj X j).val)
          (E.data.forward.tensorInv Y Z) w)
          (convolutionIndexedRightComparisonData C hC t.data
            (E.data.forward.obj X) (E.data.forward.obj Y) (E.data.forward.obj Z) g h k v w ev ew).hom) := by
  have hn := convolutionIndexedComparison_naturality C hC t.data
    (fun j => C.id (E.data.forward.obj X j).val) (E.data.forward.tensorInv Y Z)
    (fun j => hC.id_even (E.data.forward.obj X j).val) (E.laws.forward.tensor_inv_even Y Z) g v w ew
  simp only [zero_add, mul_zero, ZMod.val_zero, pow_zero, hC.one_smul] at hn
  have ht {P Q R : C.Obj} (f : C.Hom P Q) (q : C.Hom Q R) :
      C.tensorHom (C.id (E.data.forward.obj X g).val) (C.comp f q) =
        C.comp (C.tensorHom (C.id (E.data.forward.obj X g).val) f)
          (C.tensorHom (C.id (E.data.forward.obj X g).val) q) :=
    (tensorLeftLaws ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
      (E.data.forward.obj X g).val).map_comp f q
  dsimp only [equivalenceIndexedRightComparisonData, equivalenceIndexedComparisonData,
    equivalenceTensoratorComponentData, convolutionIndexedRightComparisonData,
    IsoData.trans, IsoData.tensor, IsoData.refl, IsoData.assoc, IsoData.symm]
  rw [ht]
  simp only [hC.comp_assoc]
  apply congrArg (C.comp _)
  rw [← hC.comp_assoc]
  exact (congrArg (fun z => C.comp z _) hn.symm).trans (hC.comp_assoc _ _ _)

end RMod.Classification
