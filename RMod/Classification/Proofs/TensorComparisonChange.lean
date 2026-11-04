import RMod.Classification.Instances.TensorComparisonChangeData
import RMod.Classification.Proofs.HomogeneousTensorIso
import RMod.Classification.Proofs.HomogeneousTensorPairNaturality
import RMod.Classification.Proofs.ComparisonHomogeneousIso

/-!
# Transporting binary comparisons adds the three component parities

The output inverse has the same parity as the output comparison. The
two input comparisons contribute their sum. Their signed naturality
squares compose, so the new binary comparison has exactly that total
degree on all pairs of homogeneous morphisms.
-/

set_option autoImplicit false

namespace RMod.Classification.TensorComparison

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject A} {U V : SimpleObject C}
  {E E' : SpanSuperfunctor A C S.data.object U.data.object}
  {H H' : SpanSuperfunctor A C T.data.object V.data.object}
  {N N' : SpanSuperfunctor A C (simpleTensorRepresentative A S T).data.object
    (simpleTensorRepresentative C U V).data.object}
  {a b c d : ZMod 2}
  (κ : TensorComparison S T U V E H N c)
  (i : SpanHomogeneousNatIso E E' a) (j : SpanHomogeneousNatIso H H' b)
  (n : SpanHomogeneousNatIso N N' d)

theorem changeFunctors_homogeneousIso
    (X : HomogeneousSpanCategory A S.data.object) (Y : HomogeneousSpanCategory A T.data.object) :
    HomogeneousIsoLaws C.data ((d + c) + (a + b))
      ((changeFunctorsData κ.data a b i.data j.data n.data).app X Y) := by
  have hn : HomogeneousIsoLaws C.data d
      (⟨(n.data.inv.app (spanTensorObj A S T X Y)).hom,
        (n.data.app (spanTensorObj A S T X Y)).hom⟩ : IsoData C.data _ _) :=
    ⟨⟨congrArg (fun f => f.hom) (n.laws.inv_hom (spanTensorObj A S T X Y)),
      congrArg (fun f => f.hom) (n.laws.hom_inv (spanTensorObj A S T X Y))⟩,
      n.laws.inverse.grade (spanTensorObj A S T X Y), n.laws.grade (spanTensorObj A S T X Y)⟩
  have hi : HomogeneousIsoLaws C.data a
      (⟨(i.data.app X).hom, (i.data.inv.app X).hom⟩ : IsoData C.data _ _) :=
    ⟨⟨congrArg (fun f => f.hom) (i.laws.hom_inv X), congrArg (fun f => f.hom) (i.laws.inv_hom X)⟩,
      i.laws.grade X, i.laws.inverse.grade X⟩
  have hj : HomogeneousIsoLaws C.data b
      (⟨(j.data.app Y).hom, (j.data.inv.app Y).hom⟩ : IsoData C.data _ _) :=
    ⟨⟨congrArg (fun f => f.hom) (j.laws.hom_inv Y), congrArg (fun f => f.hom) (j.laws.inv_hom Y)⟩,
      j.laws.grade Y, j.laws.inverse.grade Y⟩
  exact (hn.trans C.laws (κ.homogeneousIsoLaws X Y)).trans C.laws (hi.tensor C.laws hj)

theorem changeFunctorsLaws :
    TensorComparisonLaws S T U V ((d + c) + (a + b))
      (changeFunctorsData κ.data a b i.data j.data n.data) where
  iso X Y := (changeFunctors_homogeneousIso κ i j n X Y).toIsoLaws
  hom_grade X Y := (changeFunctors_homogeneousIso κ i j n X Y).hom_grade
  inv_grade X Y := (changeFunctors_homogeneousIso κ i j n X Y).inv_grade
  naturality {X X' Y Y' p q} f g hf hg := by
    have hi := congrArg (fun f => f.hom) (i.laws.naturality f hf)
    have hj := congrArg (fun f => f.hom) (j.laws.naturality g hg)
    have hn := congrArg (fun f => f.hom)
      (n.laws.inverse.naturality (spanTensorHom A S T f g) (A.laws.tensor_grade _ _ hf hg))
    have hit := signed_naturality_tensor C.laws
      (i.data.app X).hom (i.data.app X').hom (j.data.app Y).hom (j.data.app Y').hom
      (E.data.map f).hom (E'.data.map f).hom (H.data.map g).hom (H'.data.map g).hom
      (i.laws.grade X) (j.laws.grade Y') (E.laws.map_grade f hf) (H'.laws.map_grade g hg) hi hj
    have h := signed_naturality_trans C.laws
      (signed_naturality_trans C.laws hn (κ.laws.naturality f g hf hg)) hit
    rw [← parity_power_add, ← parity_power_add, ← add_mul, ← add_mul] at h
    exact h

end RMod.Classification.TensorComparison
