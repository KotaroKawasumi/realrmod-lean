import RMod.Classification.Instances.SpanEquivalenceComposition
import RMod.Classification.Instances.SpanEquivalenceSymmetry
import RMod.Classification.Instances.SpanChange
import RMod.Classification.Instances.SpanNaturalIso
import RMod.Classification.Proofs.SignedNaturalityInverse
import RMod.Classification.Proofs.ParityPowers

/-!
# Transferring a signed comparison through a source equivalence

For equivalences V and H with the same endpoints, a comparison from
V inverse followed by H to the identity yields a comparison from H to V.
Its maps use the specified even unit of V. Thus the comparison remains
signed-natural on all homogeneous morphisms, not just on simple objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMod.Classification.SpanSuperequivalence

open CategoryTheory

variable {A C : WeaklyPointedSuperfusion.{0, 0}} {S : A.data.Obj} {T : C.data.Obj}
  (V H : SpanSuperequivalence A C S T)

def comparisonTransferData
    (d : SpanHomogeneousNatIsoData (V.symm.trans H).forwardFunctor.data
      (spanChangeSuperequivalence C (fun _ : C.data.Obj => Iff.rfl)).forwardFunctor.data) :
    SpanHomogeneousNatIsoData H.forwardFunctor.data V.forwardFunctor.data where
  app X := H.data.functor.map (V.data.unitIso.hom.app X) ≫ d.app (V.data.functor.obj X)
  inv.app X := d.inv.app (V.data.functor.obj X) ≫ H.data.functor.map (V.data.unitIso.inv.app X)

theorem comparisonTransferLaws {a : ZMod 2}
    (η : SpanHomogeneousNatIso (V.symm.trans H).forwardFunctor
      (spanChangeSuperequivalence C (fun _ : C.data.Obj => Iff.rfl)).forwardFunctor a) :
    SpanHomogeneousNatIsoLaws a (comparisonTransferData V H η.data) := by
  have hhom (X) :
      (comparisonTransferData V H η.data).app X ≫
        (comparisonTransferData V H η.data).inv.app X = 𝟙 _ :=
    ((H.data.functor.mapIso (V.data.unitIso.app X)).trans
      (η.appIso (V.data.functor.obj X))).hom_inv_id
  have hinv (X) :
      (comparisonTransferData V H η.data).inv.app X ≫
        (comparisonTransferData V H η.data).app X = 𝟙 _ :=
    ((H.data.functor.mapIso (V.data.unitIso.app X)).trans
      (η.appIso (V.data.functor.obj X))).inv_hom_id
  have hnat {X Y : HomogeneousSpanCategory A S} {b : ZMod 2} (f : X ⟶ Y)
      (hf : A.data.IsHomogeneous b f.hom) :
      H.forwardFunctor.data.map f ≫ (comparisonTransferData V H η.data).app Y =
        ((-1 : ℝ) ^ (a * b).val) •
          ((comparisonTransferData V H η.data).app X ≫ V.forwardFunctor.data.map f) := by
    have hu : H.data.functor.map f ≫ H.data.functor.map (V.data.unitIso.hom.app Y) =
        H.data.functor.map (V.data.unitIso.hom.app X) ≫
          H.data.functor.map (V.data.inverse.map (V.data.functor.map f)) :=
      (H.data.functor.map_comp _ _).symm.trans
        ((congrArg H.data.functor.map (V.data.unitIso.hom.naturality f)).trans
          (H.data.functor.map_comp _ _))
    have hn := η.laws.naturality (V.data.functor.map f) (V.laws.forward.map_grade f hf)
    calc
      _ = (H.data.functor.map f ≫ H.data.functor.map (V.data.unitIso.hom.app Y)) ≫
          η.data.app (V.data.functor.obj Y) := (Category.assoc _ _ _).symm
      _ = (H.data.functor.map (V.data.unitIso.hom.app X) ≫
          H.data.functor.map (V.data.inverse.map (V.data.functor.map f))) ≫
            η.data.app (V.data.functor.obj Y) := congrArg (fun q => q ≫ η.data.app _) hu
      _ = H.data.functor.map (V.data.unitIso.hom.app X) ≫
          (H.data.functor.map (V.data.inverse.map (V.data.functor.map f)) ≫
            η.data.app (V.data.functor.obj Y)) := Category.assoc _ _ _
      _ = H.data.functor.map (V.data.unitIso.hom.app X) ≫
          (((-1 : ℝ) ^ (a * b).val) •
            (η.data.app (V.data.functor.obj X) ≫ V.data.functor.map f)) :=
        congrArg (fun q => H.data.functor.map (V.data.unitIso.hom.app X) ≫ q) hn
      _ = _ := by rw [Linear.comp_smul, ← Category.assoc]; rfl
  refine ⟨⟨?_, @hnat⟩, ⟨?_, ?_⟩, hhom, hinv⟩
  · intro X
    have h := C.laws.comp_grade _ _
      (H.laws.forward.map_grade _ (V.laws.unit_hom_even X)) (η.laws.grade _)
    rw [zero_add] at h
    exact h
  · intro X
    have h := C.laws.comp_grade _ _ (η.laws.inverse.grade _)
      (H.laws.forward.map_grade _ (V.laws.unit_inv_even X))
    rw [add_zero] at h
    exact h
  · intro X Y b f hf
    apply ObjectProperty.hom_ext
    exact signed_naturality_symm C.laws
      (d := ⟨((comparisonTransferData V H η.data).app X).hom,
        ((comparisonTransferData V H η.data).inv.app X).hom⟩)
      (d' := ⟨((comparisonTransferData V H η.data).app Y).hom,
        ((comparisonTransferData V H η.data).inv.app Y).hom⟩)
      ⟨congrArg (fun f => f.hom) (hhom X), congrArg (fun f => f.hom) (hinv X)⟩
      ⟨congrArg (fun f => f.hom) (hhom Y), congrArg (fun f => f.hom) (hinv Y)⟩
      (parity_power_mul_self (a * b)) (congrArg (fun f => f.hom) (hnat f hf))

def comparisonTransfer {a : ZMod 2}
    (η : SpanHomogeneousNatIso (V.symm.trans H).forwardFunctor
      (spanChangeSuperequivalence C (fun _ : C.data.Obj => Iff.rfl)).forwardFunctor a) :
    SpanHomogeneousNatIso H.forwardFunctor V.forwardFunctor a :=
  ⟨comparisonTransferData V H η.data, comparisonTransferLaws V H η⟩

end RMod.Classification.SpanSuperequivalence
