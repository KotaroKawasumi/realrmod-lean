import RMod.Classification.Proofs.ConvolutionProductLeftTransport
import RMod.Classification.Proofs.ConvolutionProductRightTransport
import RMod.Classification.Proofs.ConvolutionProductAssociatorBlock
import RMod.Classification.Proofs.ConvolutionBlocksOfParity

/-!
# The actual convolution associator on a product-indexed triple summand

The source and target transport formulas identify the two actual triple
inclusions. The block formula then cancels the left source comparison.
Naturality in the final output index moves the group associativity
comparison through the right inclusion. The resulting map is precisely
the local associator followed by the product-indexed right inclusion.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)
  (hν : ∀ g h k : t.group, t.nu g h + t.nu (g * h) k = t.nu h k + t.nu g (h * k))

theorem convolutionProductInsertion_associator (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.comp
      (C.comp (convolutionProductLeftInsertion C hC t X Y Z g h k)
        (convolutionAssociatorDataOfParity C hC t hν X Y Z ((g * h) * k)).hom)
      (IsoData.ofEq C.toWeaklyPointedSuperfusionData
        (congrArg (fun q => (convolutionObj C hC t X (convolutionObj C hC t Y Z) q).val)
          (mul_assoc g h k))).hom =
    C.comp (C.pi.localAssociator (X g).val (Y h).val (Z k).val
      (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k))
      (hν g h k) (t.omega g h k)).hom
      (convolutionProductRightInsertion C hC t X Y Z g h k) := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let L : C.Obj := C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val) (C.pi.factor (t.nu (g * h) k))
  let R : C.Obj := C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h k)) (C.pi.factor (t.nu g (h * k)))
  let P : C.Obj := (convolutionLeftFamily C hC t X Y Z ((g * h) * k) (g * h) g).obj
  let Q : t.group → C.Obj := fun q => (convolutionRightFamily C hC t X Y Z q g h).obj
  let D : C.Obj := (convolutionObj C hC t (convolutionObj C hC t X Y) Z ((g * h) * k)).val
  let E : t.group → C.Obj := fun q => (convolutionObj C hC t X (convolutionObj C hC t Y Z) q).val
  let eL : L = P := by
    dsimp [L, P, convolutionLeftFamily]
    simp only [inv_mul_cancel_left]
    exact congrArg (fun B => C.tensorObj (C.tensorObj (twistSummand C t X Y g h) B)
      (C.pi.factor (t.nu (g * h) k)))
      (congrArg (fun q => (Z q).val) (inv_mul_cancel_left (g * h) k)).symm
  let eR : R = Q ((g * h) * k) := by
    dsimp [R, Q, convolutionRightFamily]
    simp only [mul_assoc, inv_mul_cancel_left]
  let eR' : R = Q (g * (h * k)) := by
    dsimp [R, Q, convolutionRightFamily]
    simp only [inv_mul_cancel_left]
  let eI : Q ((g * h) * k) = Q (g * (h * k)) := congrArg Q (mul_assoc g h k)
  let eO : E ((g * h) * k) = E (g * (h * k)) := congrArg E (mul_assoc g h k)
  let i : C.Hom L D := convolutionProductLeftInsertion C hC t X Y Z g h k
  let il : C.Hom P D := (convolutionLeftInsertionEven C hC t X Y Z ((g * h) * k) (g * h) g).hom
  let ir : ∀ q, C.Hom (Q q) (E q) := fun q => (convolutionRightInsertionEven C hC t X Y Z q g h).hom
  let r : C.Hom R (E (g * (h * k))) := convolutionProductRightInsertion C hC t X Y Z g h k
  let a : C.Hom D (E ((g * h) * k)) := (convolutionAssociatorDataOfParity C hC t hν X Y Z ((g * h) * k)).hom
  let b : C.Hom P (Q ((g * h) * k)) := (convolutionBlockIsoOfParity C hC t hν X Y Z ((g * h) * k) g h).hom.hom
  let c : C.Hom L R := (C.pi.localAssociator (X g).val (Y h).val (Z k).val
    (t.nu g h) (t.nu (g * h) k) (t.nu h k) (t.nu g (h * k)) (hν g h k) (t.omega g h k)).hom
  have hpL : i = C.comp (IsoData.ofEq A.data eL).hom il := convolutionProductLeftInsertion_eq C hC t X Y Z g h k eL
  have hpR : r = C.comp (IsoData.ofEq A.data eR').hom (ir (g * (h * k))) := convolutionProductRightInsertion_eq C hC t X Y Z g h k eR'
  have ha : C.comp il a = C.comp b (ir ((g * h) * k)) :=
    convolutionAssociatorOfParity_inclusion_hom C hC t hν X Y Z ((g * h) * k) g h
  have hb : C.comp (IsoData.ofEq A.data eL).hom b = C.comp c (IsoData.ofEq A.data eR).hom :=
    (congrArg (C.comp (IsoData.ofEq A.data eL).hom)
      (convolutionBlockIsoOfParity_product_hom C hC t hν X Y Z g h k eL.symm eR)).trans
      ((isoData_ofEq_hom_comp_assoc A eL eL.symm _).trans (hC.id_comp _))
  have hn : C.comp (ir ((g * h) * k)) (IsoData.ofEq A.data eO).hom =
      C.comp (IsoData.ofEq A.data eI).hom (ir (g * (h * k))) :=
    indexed_morphism_eq_naturality A Q E ir (mul_assoc g h k) eI eO
  have hi : C.comp i a = C.comp c (C.comp (IsoData.ofEq A.data eR).hom (ir ((g * h) * k))) :=
    (congrArg (fun m => C.comp m a) hpL).trans
      ((hC.comp_assoc _ _ _).trans
        ((congrArg (C.comp (IsoData.ofEq A.data eL).hom) ha).trans
          ((hC.comp_assoc _ _ _).symm.trans
            ((congrArg (fun m => C.comp m (ir ((g * h) * k))) hb).trans (hC.comp_assoc _ _ _)))))
  change C.comp (C.comp i a) (IsoData.ofEq A.data eO).hom = C.comp c r
  exact (congrArg (fun m => C.comp m (IsoData.ofEq A.data eO).hom) hi).trans
    ((hC.comp_assoc _ _ _).trans
      (congrArg (C.comp c)
        ((hC.comp_assoc _ _ _).trans
          ((congrArg (C.comp (IsoData.ofEq A.data eR).hom) hn).trans
            ((isoData_ofEq_hom_comp_assoc A eR eI _).trans hpR.symm)))))

end RMod.Classification
