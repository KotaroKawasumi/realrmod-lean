import RMod.Classification.Proofs.ConvolutionProductIndex
import RMod.Classification.Proofs.TensorWhiskerEquality

/-!
# The product-indexed left triple inclusion in the actual convolution

First move the outer complementary-degree comparison through the inner
whiskered inclusion. Then move the inner comparison through its identity
whiskerings. The two source comparisons compose to the single equality
identifying the pure triple summand with the iterated convolution summand.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionProductLeftInsertion_eq (X Y Z : PullbackObj C t) (g h k : t.group)
    (hs : C.tensorObj (C.tensorObj (twistSummand C t X Y g h) (Z k).val)
        (C.pi.factor (t.nu (g * h) k)) =
      (convolutionLeftFamily C hC t X Y Z ((g * h) * k) (g * h) g).obj) :
    convolutionProductLeftInsertion C hC t X Y Z g h k =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom
        (convolutionLeftInsertionEven C hC t X Y Z ((g * h) * k) (g * h) g).hom := by
  let A : WeaklyPointedSuperfusion := ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
  let a : t.group := g * h
  let K : t.group := a * k
  let c : t.group := a⁻¹ * K
  let S : C.Obj := twistSummand C t X Y g h
  let U : C.Obj := (convolutionObj C hC t X Y a).val
  let L : t.group → C.Obj := fun q => C.tensorObj (C.tensorObj S (Z q).val) (C.pi.factor (t.nu a q))
  let M : t.group → C.Obj := fun q => C.tensorObj (C.tensorObj U (Z q).val) (C.pi.factor (t.nu a q))
  let w : ∀ q, C.Hom (L q) (M q) := fun q =>
    C.tensorHom (C.tensorHom (convolutionProductInclusion C hC t X Y g h) (C.id (Z q).val))
      (C.id (C.pi.factor (t.nu a q)))
  let e : k = c := (inv_mul_cancel_left a k).symm
  let eL : L k = L c := congrArg L e
  let eM : M k = M c := congrArg M e
  let V : C.Obj := (convolutionLeftFamily C hC t X Y Z K a g).obj
  let eI : S = twistSummand C t X Y g (g⁻¹ * a) :=
    congrArg (twistSummand C t X Y g) (inv_mul_cancel_left g h).symm
  let eW : L c = V := congrArg
    (fun B => C.tensorObj (C.tensorObj B (Z c).val) (C.pi.factor (t.nu a c))) eI
  let v : C.Hom V (M c) := C.tensorHom
    (C.tensorHom (convolutionInclusion C hC t X Y a g) (C.id (Z c).val))
    (C.id (C.pi.factor (t.nu a c)))
  let j : C.Hom (M c) (convolutionObj C hC t (convolutionObj C hC t X Y) Z K).val :=
    convolutionInclusion C hC t (convolutionObj C hC t X Y) Z K a
  have hn : C.comp (w k) (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom =
      C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (w c) :=
    indexed_morphism_eq_naturality A L M w e eL eM
  have hw : w c = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom v :=
    tensor_right_right_eq_comp A eI (convolutionInclusion C hC t X Y a g)
      (Z c).val (C.pi.factor (t.nu a c)) eW
  change C.comp (w k) (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom j) =
    C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData hs).hom (C.comp v j)
  calc
    _ = C.comp (C.comp (w k) (IsoData.ofEq C.toWeaklyPointedSuperfusionData eM).hom) j :=
      (hC.comp_assoc _ _ _).symm
    _ = C.comp (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (w c)) j :=
      congrArg (fun f => C.comp f j) hn
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (C.comp (w c) j) := hC.comp_assoc _ _ _
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom
        (C.comp (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom v) j) :=
      congrArg (fun f => C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom (C.comp f j)) hw
    _ = C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom
        (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eW).hom (C.comp v j)) :=
      congrArg (C.comp (IsoData.ofEq C.toWeaklyPointedSuperfusionData eL).hom) (hC.comp_assoc _ _ _)
    _ = _ := isoData_ofEq_hom_comp_assoc A eL eW (C.comp v j)

end RMod.Classification
