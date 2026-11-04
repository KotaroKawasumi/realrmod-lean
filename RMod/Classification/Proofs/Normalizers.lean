import RMod.Classification.Proofs.IsoCalculus
import RMod.Classification.Proofs.Pi

/-!
# Inverse and parity laws for the actual normalizers

The elementary parity multiplication is checked in its four cases.
The left and right normalizers then inherit even inverse laws from their
explicit lists of structural maps. Finally the cocycle equality identifies
their endpoints, and the nonzero scalar rescales the inverse reciprocally.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem multiplyFactors_evenIso (a b : ZMod 2) :
    EvenIsoLaws C (p.multiplyFactors a b) := by
  rcases parity_cases a with rfl | rfl <;> rcases parity_cases b with rfl | rfl
  · change EvenIsoLaws C (IsoData.leftUnit C C.tensorUnit)
    exact EvenIsoLaws.leftUnit hC _
  · change EvenIsoLaws C (IsoData.leftUnit C p.object)
    exact EvenIsoLaws.leftUnit hC _
  · change EvenIsoLaws C (IsoData.rightUnit C p.object)
    exact EvenIsoLaws.rightUnit hC _
  · change EvenIsoLaws C (⟨p.contractionHom, p.contractionInv⟩ : IsoData C _ _)
    exact
      { toIsoLaws := hp.contraction_iso hC
        hom_even := hp.contraction_hom_even hC
        inv_even := hp.contraction_inv_even hC }

theorem moveFactor_evenIso (a : ZMod 2) (X : C.Obj) :
    EvenIsoLaws C (p.moveFactor a X) := by
  rcases parity_cases a with rfl | rfl
  · change EvenIsoLaws C ((IsoData.leftUnit C X).trans C ((IsoData.rightUnit C X).symm C))
    exact (EvenIsoLaws.leftUnit hC X).trans hC (EvenIsoLaws.rightUnit hC X).symm
  · change EvenIsoLaws C (⟨p.centralHom X, p.centralInv X⟩ : IsoData C _ _)
    exact
      { toIsoLaws := hp.central_iso hC X
        hom_even := hp.central_hom_even hC X
        inv_even := hp.central_inv_even hC X }

theorem normalLeft_evenIso (X Y Z : C.Obj) (a b : ZMod 2) :
    EvenIsoLaws C (p.normalLeft X Y Z a b) := by
  let P := p.factor a
  let Q := p.factor b
  let U := C.tensorObj X (C.tensorObj Y Z)
  have h₁ := (EvenIsoLaws.assoc hC (C.tensorObj X Y) P Z).tensor hC (EvenIsoLaws.refl hC Q)
  have h₂ := ((EvenIsoLaws.refl hC (C.tensorObj X Y)).tensor hC
    (hp.moveFactor_evenIso hC a Z)).tensor hC (EvenIsoLaws.refl hC Q)
  have h₃ := (EvenIsoLaws.assoc hC (C.tensorObj X Y) Z P).symm.tensor hC (EvenIsoLaws.refl hC Q)
  have h₄ := ((EvenIsoLaws.assoc hC X Y Z).tensor hC (EvenIsoLaws.refl hC P)).tensor hC
    (EvenIsoLaws.refl hC Q)
  have h₅ := EvenIsoLaws.assoc hC U P Q
  have h₆ := (EvenIsoLaws.refl hC U).tensor hC (hp.multiplyFactors_evenIso hC a b)
  exact (((((h₁.trans hC h₂).trans hC h₃).trans hC h₄).trans hC h₅).trans hC h₆)

theorem normalRight_evenIso (X Y Z : C.Obj) (a b : ZMod 2) :
    EvenIsoLaws C (p.normalRight X Y Z a b) := by
  have h₁ := (EvenIsoLaws.assoc hC X (C.tensorObj Y Z) (p.factor a)).symm.tensor hC
    (EvenIsoLaws.refl hC (p.factor b))
  have h₂ := EvenIsoLaws.assoc hC (C.tensorObj X (C.tensorObj Y Z)) (p.factor a) (p.factor b)
  have h₃ := (EvenIsoLaws.refl hC (C.tensorObj X (C.tensorObj Y Z))).tensor hC
    (hp.multiplyFactors_evenIso hC a b)
  exact (h₁.trans hC h₂).trans hC h₃

theorem localAssociator_evenIso (X Y Z : C.Obj) (a b c d : ZMod 2)
    (e : a + b = c + d) (omega : ℝˣ) :
    EvenIsoLaws C (p.localAssociator X Y Z a b c d e omega) := by
  apply EvenIsoLaws.scale hC
  apply EvenIsoLaws.trans hC (hp.normalLeft_evenIso hC X Y Z a b)
  exact (EvenIsoLaws.ofEq hC _).trans hC (hp.normalRight_evenIso hC X Y Z c d).symm

end RMod.Classification.PiLaws
