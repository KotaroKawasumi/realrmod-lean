import RMod.Classification.Instances.ParityTripleLeftData
import RMod.Classification.Proofs.NormalizerNaturality

/-!
# Evenness and naturality of the left normalized triple route

Every structural map in this route is even. Naturality therefore follows
by composing the inverse tensorator squares, their whiskerings, and the
proved naturality square for the actual normalizer L.
-/

set_option autoImplicit false

namespace RMod.Classification

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T R : SimpleObject A} {U V W : SimpleObject C}
  {p : Pi C.data} {a b : ZMod 2}
  {E : SpanSuperfunctor A C S.data.object U.data.object}
  {H : SpanSuperfunctor A C T.data.object V.data.object}
  {K : SpanSuperfunctor A C R.data.object W.data.object}
  {F : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {N : SpanSuperfunctor A C
    (simpleTensorRepresentative A (simpleTensorRepresentative A S T) R).data.object
    (simpleTensorRepresentative C (simpleTensorRepresentative C U V) W).data.object}
  (η : ParityTensorComparison S T U V p E H F a)
  (θ : ParityTensorComparison (simpleTensorRepresentative A S T) R
    (simpleTensorRepresentative C U V) W p F K N b)

theorem parityTripleLeftTensorator_evenIso
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object)
    (Z : HomogeneousSpanCategory A R.data.object) :
    EvenIsoLaws C.data (parityTripleLeftTensorator S T R U V W η.data θ.data X Y Z) :=
  (((η.laws.iso X Y).tensor C.laws (EvenIsoLaws.refl C.laws (K.data.obj Z).obj)).tensor C.laws
    (EvenIsoLaws.refl C.laws (p.data.factor b))).trans C.laws (θ.laws.iso (spanTensorObj A S T X Y) Z)

theorem parityTripleLeftLaws :
    ParityTripleComparisonLaws S T R U V W (parityTripleLeftData S T R U V W η.data θ.data) where
  iso X Y Z := ((θ.laws.iso (spanTensorObj A S T X Y) Z).symm.trans C.laws
    (((η.laws.iso X Y).symm.tensor C.laws (EvenIsoLaws.refl C.laws (K.data.obj Z).obj)).tensor C.laws
      (EvenIsoLaws.refl C.laws (p.data.factor b)))).trans C.laws
        (p.laws.normalLeft_evenIso C.laws (E.data.obj X).obj (H.data.obj Y).obj (K.data.obj Z).obj a b)
  naturality := by
    intro X X' Y Y' Z Z' c d e f g h hf hg hh
    have houter := iso_naturality_symm C.laws (θ.laws.iso _ _).toIsoLaws (θ.laws.iso _ _).toIsoLaws
      (θ.laws.naturality (spanTensorHom A S T f g) h (A.laws.tensor_grade _ _ hf hg) hh)
    have hinner := iso_naturality_symm C.laws (η.laws.iso X Y).toIsoLaws (η.laws.iso X' Y').toIsoLaws
      (η.laws.naturality f g hf hg)
    have hi := iso_naturality_tensor C.laws (η.laws.iso X Y).symm
      (EvenIsoLaws.refl C.laws (K.data.obj Z').obj) hinner (iso_naturality_refl C.laws (K.data.map h).hom)
    have hw := iso_naturality_whiskerRight C.laws
      ((η.laws.iso X Y).symm.tensor C.laws (EvenIsoLaws.refl C.laws (K.data.obj Z).obj)) hi (p.data.factor b)
    exact iso_naturality_trans C.laws (iso_naturality_trans C.laws houter hw)
      (p.laws.normalLeft_naturality C.laws (E.data.map f).hom (H.data.map g).hom (K.data.map h).hom a b)

end RMod.Classification
