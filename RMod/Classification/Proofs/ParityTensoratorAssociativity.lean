import RMod.Classification.Instances.ParityTripleLeft
import RMod.Classification.Instances.ParityTripleRight
import RMod.Classification.Instances.ParityTripleTransport
import RMod.Classification.Proofs.NormalizedScalarTransport

/-!
# The extracted normalized scalar gives the actual associativity square

The left and right tensorators are the specified even composites. The
normal-form equality is precisely the equality used inside the model
associator. Cancelling the inverse maps yields E(alpha) T_L =
T_R (omega R⁻¹ L), with no replacement of the actual normalizers.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C} {p : Pi C.data} {a b c d : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {J : SpanSuperfunctor A C (simpleTensorRepresentative A T R).data.object
    (simpleTensorRepresentative C V W).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A S (simpleTensorRepresentative A T R)).data.object
    (simpleTensorRepresentative C U (simpleTensorRepresentative C V W)).data.object}
  (ηL : ParityTensorComparison S T U V p E H F a)
  (θL : ParityTensorComparison (simpleTensorRepresentative A S T) R
    (simpleTensorRepresentative C U V) W p F K (tripleRightFunctor S T R U V W N) b)
  (ηR : ParityTensorComparison T R V W p H K J c)
  (θR : ParityTensorComparison S (simpleTensorRepresentative A T R) U
    (simpleTensorRepresentative C V W) p E J N d)

theorem parityTensorator_associativity (e : a + b = c + d) (ω : ℝˣ)
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object)
    (heq : ((parityTripleRight ηR θR).data.app X Y Z).hom = C.data.smul (ω : ℝ)
      ((parityTripleTransport e (parityTripleLeft ηL θL)).data.app X Y Z).hom) :
    C.data.comp (parityTripleLeftTensorator S T R U V W ηL.data θL.data X Y Z).hom
      (SpanSuperfunctor.mapIsoData N.data
        (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
        (IsoData.assoc A.data X.obj Y.obj Z.obj)).hom =
      C.data.comp (p.data.localAssociator (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj
        a b c d e ω).hom (parityTripleRightTensorator S T R U V W ηR.data θR.data X Y Z).hom := by
  apply normalized_scalar_transport C.laws
    (parityTripleLeftTensorator S T R U V W ηL.data θL.data X Y Z)
    (parityTripleRightTensorator S T R U V W ηR.data θR.data X Y Z)
    (p.data.normalLeft (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj a b)
    (p.data.normalRight (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj c d)
    (IsoData.ofEq C.data _) _ ω
    (parityTripleLeftTensorator_evenIso ηL θL X Y Z).toIsoLaws
    (parityTripleRightTensorator_evenIso ηR θR X Y Z).toIsoLaws
    (p.laws.normalRight_evenIso C.laws _ _ _ c d).toIsoLaws
  let α := (SpanSuperfunctor.mapIsoData N.data
    (X := tripleSpanObjInRight A S T R X Y Z) (Y := rightTripleSpanObj A S T R X Y Z)
    (IsoData.assoc A.data X.obj Y.obj Z.obj)).hom
  let l := (θL.data.app (spanTensorObj A S T X Y) Z).inv
  let r := (θR.data.app X (spanTensorObj A T R Y Z)).inv
  let iL := C.data.tensorHom
    (C.data.tensorHom (ηL.data.app X Y).inv (C.data.id (K.data.obj Z).obj)) (C.data.id (p.data.factor b))
  let iR := C.data.tensorHom
    (C.data.tensorHom (C.data.id (E.data.obj X).obj) (ηR.data.app Y Z).inv) (C.data.id (p.data.factor d))
  let L := (p.data.normalLeft (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj a b).hom
  let Rn := (p.data.normalRight (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj c d).hom
  let q := (IsoData.ofEq C.data (congrArg (fun z => C.data.tensorObj
    (C.data.tensorObj (E.data.obj X).obj (C.data.tensorObj (H.data.obj Y).obj (K.data.obj Z).obj))
    (p.data.factor z)) e)).hom
  change C.data.comp (C.data.comp (C.data.comp α r) iR) Rn =
    C.data.smul (ω : ℝ) (C.data.comp (C.data.comp (C.data.comp l iL) L) q) at heq
  change C.data.comp (C.data.comp α (C.data.comp r iR)) Rn =
    C.data.smul (ω : ℝ) (C.data.comp (C.data.comp (C.data.comp l iL) L) q)
  rw [C.laws.comp_assoc α r iR] at heq
  exact heq

end RMod.Classification
