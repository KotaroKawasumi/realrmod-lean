import RMod.BrundanEllis.StackingReferenceTensorRows
import RMod.Classification.Proofs.RealReference
import RMod.Classification.Proofs.Components

/-! Objects of an intrinsic Brauer--Wall component in the concrete reference
category have a uniform stored label.  This identifies them with the finite
row presentations used for the explicit exchange. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMod.BrundanEllis.Stacking.ReferenceCommutor
open Superfusion Superfusion.RModCoordinate Superfusion.RMod.RawDCT Superfusion.RMod.FromRawDCT
open RMod.Classification

/-- Each stored atom of an object in component `a` has label `a`. -/
theorem inComponent_label {a : ZMod 8} {X : Obj} (hX : InComponent realRModData a X)
    (i : Fin X.size) : (X.atom i).label = a := by
  by_contra hne
  have hz := (InComponent.iff_orthogonal realReference X a).mp hX
    (Obj.singleton (X.atom i)) (X.atom i).label
    (realSingleton_simple (X.atom i).label (X.atom i).shift)
    ((realSingleton_type_iff (X.atom i).label (X.atom i).shift (X.atom i).label).mpr rfl)
    hne (Finite.atomInclusion X i)
  exact RealSemisimple.atomInclusion_ne_zero X i hz

/-- The uniform row presentation is literally the given object. -/
theorem rowObject_of_labels (a : ZMod 8) (X : Obj)
    (hX : ∀ i, (X.atom i).label = a) :
    rowObject a (fun i => (X.atom i).shift) = X := by
  rcases X with ⟨n, A⟩
  apply congrArg (Sigma.mk n)
  funext i
  exact Prod.ext (hX i).symm rfl

/-- Intrinsic component membership suffices to use the concrete exchange. -/
theorem rowObject_of_component {a : ZMod 8} {X : Obj} (hX : InComponent realRModData a X) :
    rowObject a (fun i => (X.atom i).shift) = X :=
  rowObject_of_labels a X (inComponent_label hX)

/-- Coefficients recover every raw morphism between constant-label families. -/
theorem rowHom_reconstruct {n m : ℕ} (a : ZMod 8)
    (p : Fin n → ZMod 2) (q : Fin m → ZMod 2)
    (f : Hom realDData (rowObject a p) (rowObject a q)) :
    rowHom a p q (fun j i => (f i j).coeff rfl) = f := by
  funext i j
  apply AtomHom.ext_same_label
  exact rowHom_coeff a p q _ i j

end RMod.BrundanEllis.Stacking.ReferenceCommutor
