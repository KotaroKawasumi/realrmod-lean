import RMod.Classification.Proofs.ConvolutionProductIndex
import RMod.Classification.Proofs.TensorWhiskerEquality

/-!
# The product-indexed right triple inclusion in the actual convolution

Expose the source comparison in the inner product inclusion. Naturality
of the remaining inclusion family then moves the outer degree comparison
to that source. The composite source equality accounts for both nested
complementary-degree conventions in the right convolution expansion.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionProductRightInsertion_eq (X Y Z : PullbackObj C t) (g h k : t.group)
    (hs : C.tensorObj (C.tensorObj (X g).val (twistSummand C t Y Z h k))
        (C.pi.factor (t.nu g (h * k))) =
      (convolutionRightFamily C hC t X Y Z (g * (h * k)) g h).obj) :
    convolutionProductRightInsertion C hC t X Y Z g h k =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (convolutionRightInsertionEven C hC t X Y Z (g * (h * k)) g h).hom := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let a : t.group := h * k
  let K : t.group := g * a
  let c : t.group := g⁻¹ * K
  let S : C.Obj := twistSummand C t Y Z h k
  let V : C.Obj := C.tensorObj (C.tensorObj (X g).val S) (C.pi.factor (t.nu g a))
  let L : t.group → C.Obj := fun q => C.tensorObj
    (C.tensorObj (X g).val (twistSummand C t Y Z h (h⁻¹ * q))) (C.pi.factor (t.nu g q))
  let M : t.group → C.Obj := fun q => C.tensorObj
    (C.tensorObj (X g).val (convolutionObj C hC t Y Z q).val) (C.pi.factor (t.nu g q))
  let w : ∀ q, C.Hom (L q) (M q) := fun q =>
    C.tensorHom (C.tensorHom (C.id (X g).val) (convolutionInclusion C hC t Y Z q h))
      (C.id (C.pi.factor (t.nu g q)))
  let e : a = c := (inv_mul_cancel_left g a).symm
  let eL : L a = L c := congrArg L e
  let eM : M a = M c := congrArg M e
  let eI : S = twistSummand C t Y Z h (h⁻¹ * a) :=
    congrArg (twistSummand C t Y Z h) (inv_mul_cancel_left h k).symm
  let eW : V = L a := congrArg
    (fun B => C.tensorObj (C.tensorObj (X g).val B) (C.pi.factor (t.nu g a))) eI
  let v : C.Hom V (M a) := C.tensorHom
    (C.tensorHom (C.id (X g).val) (convolutionProductInclusion C hC t Y Z h k))
    (C.id (C.pi.factor (t.nu g a)))
  let j : C.Hom (M c) (convolutionObj C hC t X (convolutionObj C hC t Y Z) K).val :=
    convolutionInclusion C hC t X (convolutionObj C hC t Y Z) K g
  have hn : C.comp (w a) (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (w c) :=
    indexed_morphism_eq_naturality A L M w e eL eM
  have hw : v = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom (w a) :=
    tensor_left_right_eq_comp A eI (convolutionInclusion C hC t Y Z a h)
      (X g).val (C.pi.factor (t.nu g a)) eW
  change C.comp v (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom j) =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom (C.comp (w c) j)
  calc
    _ = C.comp (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom (w a))
        (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom j) :=
      congrArg (fun f => C.comp f (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom j)) hw
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom
        (C.comp (w a) (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom j)) := hC.comp_assoc _ _ _
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom
        (C.comp (C.comp (w a) (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom) j) :=
      congrArg (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom) (hC.comp_assoc _ _ _).symm
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom
        (C.comp (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (w c)) j) :=
      congrArg (fun f => C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom (C.comp f j)) hn
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom
        (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (C.comp (w c) j)) :=
      congrArg (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom) (hC.comp_assoc _ _ _)
    _ = _ := isoData_ofEq_hom_comp_assoc A eW eL (C.comp (w c) j)

end RMod.Classification
