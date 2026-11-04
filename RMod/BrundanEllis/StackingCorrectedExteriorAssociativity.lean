import RMod.BrundanEllis.StackingCorrectedNestedInsertions
import RMod.BrundanEllis.StackingCorrectedBinaryAssociativity
import RMod.BrundanEllis.StackingTransportedCoherence
import RMod.BrundanEllis.StackingExternalEvenMaps
import RMod.BrundanEllis.StackingCorrectedProductInclusion
import RMod.Classification.Proofs.ConvolutionProductAssociator
import RMod.Classification.Proofs.ConvolutionProductTripleExt
import RMod.Classification.Proofs.IndexedMorphismEquality

/-! Coherence of the corrected exterior tensor comparison and normalization of its unit. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- The actual iterated convolution inclusions remain even. -/
theorem convolutionProductLeftInsertion_grade (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : RMod.Classification.TwistData)
    (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.IsHomogeneous 0 (convolutionProductLeftInsertion C hC t X Y Z g h k) := by
  exact comp_even hC.toWeaklyPointedSuperfusionLaws
    (hC.tensor_grade _ _ (hC.tensor_grade _ _
      (convolutionProductInclusion_grade C hC t X Y g h) (hC.id_even _)) (hC.id_even _))
    (convolutionProductInclusion_grade C hC t (convolutionObj C hC t X Y) Z (g * h) k)

theorem convolutionProductRightInsertion_grade (C : PiSuperfusionData.{0, 0})
    (hC : ReferenceProperty C) (t : RMod.Classification.TwistData)
    (X Y Z : PullbackObj C t) (g h k : t.group) :
    C.IsHomogeneous 0 (convolutionProductRightInsertion C hC t X Y Z g h k) := by
  exact comp_even hC.toWeaklyPointedSuperfusionLaws
    (hC.tensor_grade _ _ (hC.tensor_grade _ _ (hC.id_even _)
      (convolutionProductInclusion_grade C hC t Y Z h k)) (hC.id_even _))
    (convolutionProductInclusion_grade C hC t X (convolutionObj C hC t Y Z) g (h * k))

local notation "R" => reference.data
local notation "hR" => referenceProperty
local notation "pi" => reference.data.pi

/-- The tensor of the two original convolution associators has exactly
the tensor of the local associators as its transported triple block. -/
theorem pairedTripleInsertion_associator (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group) :
    (R).comp
      ((R).comp
        ((R).tensorHom
          (convolutionProductLeftInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
          (convolutionProductLeftInsertion R hR (oldTwist s).data X X' X'' g g' g''))
        ((R).tensorHom
          (convolutionAssociatorData R hR (oldTwist t).data (oldTwist t).laws Y Y' Y'' ((h * h') * h'')).hom
          (convolutionAssociatorData R hR (oldTwist s).data (oldTwist s).laws X X' X'' ((g * g') * g'')).hom))
      ((R).tensorHom
        (IsoData.ofEq (R).toWeaklyPointedSuperfusionData
          (congrArg (fun k => (convolutionObj R hR (oldTwist t).data Y
            (convolutionObj R hR (oldTwist t).data Y' Y'') k).val) (mul_assoc h h' h''))).hom
        (IsoData.ofEq (R).toWeaklyPointedSuperfusionData
          (congrArg (fun k => (convolutionObj R hR (oldTwist s).data X
            (convolutionObj R hR (oldTwist s).data X' X'') k).val) (mul_assoc g g' g''))).hom) =
    (R).comp
      ((R).tensorHom
        ((pi).localAssociator (Y h).val (Y' h').val (Y'' h'').val
          (t.nu h h') (t.nu (h * h') h'') (t.nu h' h'') (t.nu h (h' * h''))
          ((oldTwist t).laws.normalizer_parity h h' h'') (t.omega h h' h'')).hom
        ((pi).localAssociator (X g).val (X' g').val (X'' g'').val
          (s.nu g g') (s.nu (g * g') g'') (s.nu g' g'') (s.nu g (g' * g''))
          ((oldTwist s).laws.normalizer_parity g g' g'') (s.omega g g' g'')).hom)
      ((R).tensorHom
        (convolutionProductRightInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
        (convolutionProductRightInsertion R hR (oldTwist s).data X X' X'' g g' g'')) := by
  apply tensor_transported_squares
    ⟨(R).toWeaklyPointedSuperfusionData, (hR).toWeaklyPointedSuperfusionLaws⟩
  · exact (convolutionAssociator_evenIso R hR (oldTwist s).data (oldTwist s).laws X X' X'' _).hom_even
  · exact (EvenIsoLaws.ofEq (hR).toWeaklyPointedSuperfusionLaws _).hom_even
  · exact convolutionProductRightInsertion_grade R hR (oldTwist s).data X X' X'' g g' g''
  · exact convolutionProductInsertion_associator R hR (oldTwist t).data
      (oldTwist t).laws.normalizer_parity Y Y' Y'' h h' h''
  · exact convolutionProductInsertion_associator R hR (oldTwist s).data
      (oldTwist s).laws.normalizer_parity X X' X'' g g' g''

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "hR" => referenceProperty
local notation "pi" => reference.data.pi

/-- The actual paired convolution inclusions carry the local twistMul
comparison to a transported component equation for the assembled routes. -/
theorem correctedExteriorTriple_transportedCoherence (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group)
    (hl : ReferenceCommutor.LeftEquation (s.rho g).toAdd (t.rho h').toAdd (t.rho h'').toAdd)
    (hr : ReferenceCommutor.RightEquation (s.rho g).toAdd (s.rho g').toAdd (t.rho h'').toAdd) :
    let u := (exteriorTwist s t).val
    let V : s.group × t.group → (R).Obj := fun ab => (R).tensorObj
      (convolutionObj R hR (oldTwist t).data Y (convolutionObj R hR (oldTwist t).data Y' Y'') ab.2).val
      (convolutionObj R hR (oldTwist s).data X (convolutionObj R hR (oldTwist s).data X' X'') ab.1).val
    (R).comp
      ((R).comp (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
        ((R).tensorHom
          (convolutionProductLeftInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
          (convolutionProductLeftInsertion R hR (oldTwist s).data X X' X'' g g' g'')))
      ((R).comp
        ((R).tensorHom
          (convolutionAssociatorData R hR (oldTwist t).data (oldTwist t).laws Y Y' Y'' ((h * h') * h'')).hom
          (convolutionAssociatorData R hR (oldTwist s).data (oldTwist s).laws X X' X'' ((g * g') * g'')).hom)
        (IsoData.ofEq (R).toWeaklyPointedSuperfusionData
          (congrArg V (mul_assoc (g, h) (g', h') (g'', h'')))).hom) =
    (R).comp
      ((pi).localAssociator
        ((R).tensorObj (Y h).val (X g).val)
        ((R).tensorObj (Y' h').val (X' g').val)
        ((R).tensorObj (Y'' h'').val (X'' g'').val)
        (u.nu (g, h) (g', h')) (u.nu (g * g', h * h') (g'', h''))
        (u.nu (g', h') (g'', h'')) (u.nu (g, h) (g' * g'', h' * h''))
        ((oldTwist u).laws.normalizer_parity (g, h) (g', h') (g'', h''))
        (u.omega (g, h) (g', h') (g'', h''))).hom
      ((R).comp (correctedExteriorRightBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
        ((R).tensorHom
          (convolutionProductRightInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
          (convolutionProductRightInsertion R hR (oldTwist s).data X X' X'' g g' g''))) := by
  dsimp only
  let C : WeaklyPointedSuperfusion := ⟨(R).toWeaklyPointedSuperfusionData, (hR).toWeaklyPointedSuperfusionLaws⟩
  let VS := fun k => (convolutionObj R hR (oldTwist s).data X
    (convolutionObj R hR (oldTwist s).data X' X'') k).val
  let VT := fun k => (convolutionObj R hR (oldTwist t).data Y
    (convolutionObj R hR (oldTwist t).data Y' Y'') k).val
  rw [tensor_equality_comparison C
    (congrArg VT (mul_assoc h h' h'')) (congrArg VS (mul_assoc g g' g''))]
  let b := (R).tensorHom
    ((pi).localAssociator (Y h).val (Y' h').val (Y'' h'').val
      (t.nu h h') (t.nu (h * h') h'') (t.nu h' h'') (t.nu h (h' * h''))
      ((oldTwist t).laws.normalizer_parity h h' h'') (t.omega h h' h'')).hom
    ((pi).localAssociator (X g).val (X' g').val (X'' g'').val
      (s.nu g g') (s.nu (g * g') g'') (s.nu g' g'') (s.nu g (g' * g''))
      ((oldTwist s).laws.normalizer_parity g g' g'') (s.omega g g' g'')).hom
  let incR := (R).tensorHom
    (convolutionProductRightInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
    (convolutionProductRightInsertion R hR (oldTwist s).data X X' X'' g g' g'')
  have h1 := congrArg ((R).comp
    (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom)
    (pairedTripleInsertion_associator s t X X' X'' Y Y' Y'' g g' g'' h h' h'')
  have h2 := congrArg (fun m => (R).comp m incR)
    (correctedExteriorBinary_associativity s t X X' X'' Y Y' Y'' g g' g'' h h' h'' hl hr)
  calc
    _ = (R).comp ((R).comp
        (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom b) incR := by
      with_unfolding_all simpa only [(hR).comp_assoc] using h1
    _ = _ := by
      with_unfolding_all simpa only [(hR).comp_assoc] using h2

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "hR" => referenceProperty
local notation "pi" => reference.data.pi

/-- The two whole associator routes agree on every actual triple summand. -/
theorem correctedExteriorProductInsertion_associativity (s t : Twist)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t)
    (g g' g'' : s.group) (h h' h'' : t.group)
    (hl : ReferenceCommutor.LeftEquation (s.rho g).toAdd (t.rho h').toAdd (t.rho h'').toAdd)
    (hr : ReferenceCommutor.RightEquation (s.rho g).toAdd (s.rho g').toAdd (t.rho h'').toAdd) :
    let F := reversedExteriorPairing s t
    let u := (oldTwist (exteriorTwist s t).val).data
    let SX := convolutionObj R hR (oldTwist s).data X X'
    let TY := convolutionObj R hR (oldTwist t).data Y Y'
    let SX' := convolutionObj R hR (oldTwist s).data X' X''
    let TY' := convolutionObj R hR (oldTwist t).data Y' Y''
    let K := ((g * g') * g'', (h * h') * h'')
    let i := convolutionProductLeftInsertion R hR u
      (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) (g, h) (g', h') (g'', h'')
    (R).comp i
      ((R).comp
        ((R).comp
          (convolutionHom R hR u
            (fun ab => (correctedExteriorTensoratorData s t X X' Y Y' ab.1 ab.2).hom)
            (fun ab => (R).id (F.obj (X'', Y'') ab).val) K)
          (correctedExteriorTensoratorData s t SX X'' TY Y'' K.1 K.2).hom)
        ((R).tensorHom
          (convolutionAssociatorData R hR (oldTwist t).data (oldTwist t).laws Y Y' Y'' K.2).hom
          (convolutionAssociatorData R hR (oldTwist s).data (oldTwist s).laws X X' X'' K.1).hom)) =
    (R).comp i
      ((R).comp
        (convolutionAssociatorData R hR u (oldTwist (exteriorTwist s t).val).laws
          (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) K).hom
        ((R).comp
          (convolutionHom R hR u (fun ab => (R).id (F.obj (X, Y) ab).val)
            (fun ab => (correctedExteriorTensoratorData s t X' X'' Y' Y'' ab.1 ab.2).hom) K)
          (correctedExteriorTensoratorData s t X SX' Y TY' K.1 K.2).hom)) := by
  dsimp only
  let C : WeaklyPointedSuperfusion := ⟨(R).toWeaklyPointedSuperfusionData, (hR).toWeaklyPointedSuperfusionLaws⟩
  let F := reversedExteriorPairing s t
  let u := (oldTwist (exteriorTwist s t).val).data
  let SX := convolutionObj R hR (oldTwist s).data X X'
  let TY := convolutionObj R hR (oldTwist t).data Y Y'
  let SX' := convolutionObj R hR (oldTwist s).data X' X''
  let TY' := convolutionObj R hR (oldTwist t).data Y' Y''
  let D := fun ab => (convolutionObj R hR u
    (convolutionObj R hR u (F.obj (X, Y)) (F.obj (X', Y'))) (F.obj (X'', Y'')) ab).val
  let E := fun ab => (convolutionObj R hR u
    (F.obj (X, Y)) (convolutionObj R hR u (F.obj (X', Y')) (F.obj (X'', Y''))) ab).val
  let U : s.group × t.group → (R).Obj := fun ab => (R).tensorObj
    (convolutionObj R hR (oldTwist t).data TY Y'' ab.2).val
    (convolutionObj R hR (oldTwist s).data SX X'' ab.1).val
  let V : s.group × t.group → (R).Obj := fun ab => (R).tensorObj
    (convolutionObj R hR (oldTwist t).data Y TY' ab.2).val
    (convolutionObj R hR (oldTwist s).data X SX' ab.1).val
  let i := convolutionProductLeftInsertion R hR u
    (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) (g, h) (g', h') (g'', h'')
  let j := convolutionProductRightInsertion R hR u
    (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) (g, h) (g', h') (g'', h'')
  let ml : ∀ ab, (R).Hom (D ab) (U ab) := fun ab => (R).comp
    (convolutionHom R hR u
      (fun cd => (correctedExteriorTensoratorData s t X X' Y Y' cd.1 cd.2).hom)
      (fun cd => (R).id (F.obj (X'', Y'') cd).val) ab)
    (correctedExteriorTensoratorData s t SX X'' TY Y'' ab.1 ab.2).hom
  let mr : ∀ ab, (R).Hom (E ab) (V ab) := fun ab => (R).comp
    (convolutionHom R hR u (fun cd => (R).id (F.obj (X, Y) cd).val)
      (fun cd => (correctedExteriorTensoratorData s t X' X'' Y' Y'' cd.1 cd.2).hom) ab)
    (correctedExteriorTensoratorData s t X SX' Y TY' ab.1 ab.2).hom
  let K := ((g * g') * g'', (h * h') * h'')
  let K' := (g * (g' * g''), h * (h' * h''))
  let n : (R).Hom (U K) (V K) := (R).tensorHom
    (convolutionAssociatorData R hR (oldTwist t).data (oldTwist t).laws Y Y' Y'' K.2).hom
    (convolutionAssociatorData R hR (oldTwist s).data (oldTwist s).laws X X' X'' K.1).hom
  let a : (R).Hom (D K) (E K) :=
    (convolutionAssociatorData R hR u (oldTwist (exteriorTwist s t).val).laws
      (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) K).hom
  let eE : E K = E K' := congrArg E (mul_assoc (g, h) (g', h') (g'', h''))
  let eV : V K = V K' := congrArg V (mul_assoc (g, h) (g', h') (g'', h''))
  let pL := (R).comp (correctedExteriorLeftBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
    ((R).tensorHom
      (convolutionProductLeftInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
      (convolutionProductLeftInsertion R hR (oldTwist s).data X X' X'' g g' g''))
  let pR := (R).comp (correctedExteriorRightBinaryData s t X X' X'' Y Y' Y'' g g' g'' h h' h'').hom
    ((R).tensorHom
      (convolutionProductRightInsertion R hR (oldTwist t).data Y Y' Y'' h h' h'')
      (convolutionProductRightInsertion R hR (oldTwist s).data X X' X'' g g' g''))
  let c := ((pi).localAssociator
    (F.obj (X, Y) (g, h)).val (F.obj (X', Y') (g', h')).val (F.obj (X'', Y'') (g'', h'')).val
    (u.nu (g, h) (g', h')) (u.nu (g * g', h * h') (g'', h''))
    (u.nu (g', h') (g'', h'')) (u.nu (g, h) (g' * g'', h' * h''))
    ((oldTwist (exteriorTwist s t).val).laws.normalizer_parity (g, h) (g', h') (g'', h''))
    (u.omega (g, h) (g', h') (g'', h''))).hom
  have hL : (R).comp i (ml K) = pL := ((hR).comp_assoc _ _ _).symm.trans
    (correctedExteriorProductLeft_tensorators s t X X' X'' Y Y' Y'' g g' g'' h h' h'')
  have hR' : (R).comp j (mr K') = pR := ((hR).comp_assoc _ _ _).symm.trans
    (correctedExteriorProductRight_tensorators s t X X' X'' Y Y' Y'' g g' g'' h h' h'')
  have hc : (R).comp pL ((R).comp n (IsoData.ofEq C.data eV).hom) = (R).comp c pR :=
    correctedExteriorTriple_transportedCoherence s t X X' X'' Y Y' Y'' g g' g'' h h' h'' hl hr
  have hm : (R).comp ((R).comp i a) (IsoData.ofEq C.data eE).hom = (R).comp c j :=
    convolutionProductInsertion_associator R hR u (oldTwist (exteriorTwist s t).val).laws.normalizer_parity
      (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) (g, h) (g', h') (g'', h'')
  have hi : (R).comp (mr K) (IsoData.ofEq C.data eV).hom =
      (R).comp (IsoData.ofEq C.data eE).hom (mr K') :=
    indexed_morphism_eq_naturality C E V mr (mul_assoc (g, h) (g', h') (g'', h'')) eE eV
  exact coherence_of_transported_summands C i j (ml K) n a (mr K) (mr K') c pL pR eE eV
    hL hR' hc hm hi

end RMod.BrundanEllis.Stacking

namespace RMod.BrundanEllis.Stacking
open RMod.Classification
local notation "R" => reference.data
local notation "hR" => referenceProperty

/-- Agreement on the actual triple summands determines the entire
coordinate map, including all convolution direct sums. -/
theorem correctedExteriorTensorator_associativity (s t : Twist)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d)
    (X X' X'' : pullback s) (Y Y' Y'' : pullback t) (K : s.group × t.group) :
    let F := reversedExteriorPairing s t
    let u := (oldTwist (exteriorTwist s t).val).data
    let SX := convolutionObj R hR (oldTwist s).data X X'
    let TY := convolutionObj R hR (oldTwist t).data Y Y'
    let SX' := convolutionObj R hR (oldTwist s).data X' X''
    let TY' := convolutionObj R hR (oldTwist t).data Y' Y''
    (R).comp
      ((R).comp
        (convolutionHom R hR u
          (fun ab => (correctedExteriorTensoratorData s t X X' Y Y' ab.1 ab.2).hom)
          (fun ab => (R).id (F.obj (X'', Y'') ab).val) K)
        (correctedExteriorTensoratorData s t SX X'' TY Y'' K.1 K.2).hom)
      ((R).tensorHom
        (convolutionAssociatorData R hR (oldTwist t).data (oldTwist t).laws Y Y' Y'' K.2).hom
        (convolutionAssociatorData R hR (oldTwist s).data (oldTwist s).laws X X' X'' K.1).hom) =
    (R).comp
      (convolutionAssociatorData R hR u (oldTwist (exteriorTwist s t).val).laws
        (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) K).hom
      ((R).comp
        (convolutionHom R hR u (fun ab => (R).id (F.obj (X, Y) ab).val)
          (fun ab => (correctedExteriorTensoratorData s t X' X'' Y' Y'' ab.1 ab.2).hom) K)
        (correctedExteriorTensoratorData s t X SX' Y TY' K.1 K.2).hom) := by
  dsimp only
  let F := reversedExteriorPairing s t
  let u := (oldTwist (exteriorTwist s t).val).data
  let M : s.group × t.group → (R).Obj := fun ab => (R).tensorObj
    (convolutionObj R hR (oldTwist t).data Y (convolutionObj R hR (oldTwist t).data Y' Y'') ab.2).val
    (convolutionObj R hR (oldTwist s).data X (convolutionObj R hR (oldTwist s).data X' X'') ab.1).val
  apply congrFun (hom_ext_of_convolutionProductLeftInsertions R hR u
    (F.obj (X, Y)) (F.obj (X', Y')) (F.obj (X'', Y'')) M _ _ ?_) K
  intro ab cd ef
  exact correctedExteriorProductInsertion_associativity s t X X' X'' Y Y' Y''
    ab.1 cd.1 ef.1 ab.2 cd.2 ef.2 (hl _ _ _) (hr _ _ _)

end RMod.BrundanEllis.Stacking

open CategoryTheory CategoryTheory.MonoidalCategory
namespace RMod.BrundanEllis.Stacking
open RMod.Classification

/-- Coordinate evaluation of a three-map composite, with its category
fixed before substitution of the large exterior construction. -/
theorem pullbackEvenValue_comp_three (s : Twist) {A B C D : Even (pullback s)}
    (f : A ⟶ B) (g : B ⟶ C) (q : C ⟶ D) (k : s.group) :
    pullbackEvenValue s (f ≫ g ≫ q) k = reference.data.comp (pullbackEvenValue s f k)
      (reference.data.comp (pullbackEvenValue s g k) (pullbackEvenValue s q k)) :=
  (pullbackEvenValue_comp s f (g ≫ q) k).trans
    (congrArg (reference.data.comp (pullbackEvenValue s f k)) (pullbackEvenValue_comp s g q k))

/-- Evaluate the whole family before passing it to convolution. -/
theorem pullbackEvenValue_id_family (s : Twist) (X : Even (pullback s)) :
    pullbackEvenValue s (𝟙 X) = fun k => reference.data.id (X k).val :=
  funext (pullbackEvenValue_id s X)

set_option maxHeartbeats 400000 in
/-- The tensor comparison family retains its specified coordinate maps. -/
theorem correctedReversedExteriorTensorIso_hom_family (s t : Twist)
    (X Y : Even (SuperTensorProduct (pullback s) (pullback t))) :
    pullbackEvenValue (exteriorTwist s t).val (correctedReversedExteriorTensorIso s t X Y).hom =
      fun ab : s.group × t.group => (correctedExteriorTensoratorData s t X.1 Y.1 X.2 Y.2 ab.1 ab.2).hom := by
  funext ab
  rcases ab with ⟨g, h⟩
  with_unfolding_all exact correctedReversedExteriorTensorIso_hom s t X Y g h

set_option maxHeartbeats 400000 in
/-- The actual even tensor comparisons satisfy the strong monoidal
associativity equation, once the concrete reference hexagons are supplied. -/
theorem correctedReversedExteriorTensorIso_associativity (s t : Twist)
    (hl : ∀ b c d, ReferenceCommutor.LeftEquation b c d)
    (hr : ∀ b c d, ReferenceCommutor.RightEquation b c d)
    (X Y Z : Even (SuperTensorProduct (pullback s) (pullback t))) :
    let F := (reversedExteriorPairing s t).forget
    let μ := correctedReversedExteriorTensorIso s t
    (μ X Y).hom ▷ F.obj Z ≫ (μ (X ⊗ Y) Z).hom ≫ F.map (α_ X Y Z).hom =
      (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom ≫ F.obj X ◁ (μ Y Z).hom ≫
        (μ X (Y ⊗ Z)).hom := by
  let u := (exteriorTwist s t).val
  let F : Even (SuperTensorProduct (pullback s) (pullback t)) ⥤ Even (pullback u) :=
    (reversedExteriorPairing s t).forget
  let μ : ∀ A B : Even (SuperTensorProduct (pullback s) (pullback t)),
      F.obj A ⊗ F.obj B ≅ F.obj (A ⊗ B) := correctedReversedExteriorTensorIso s t
  apply pullbackEvenValue_ext u
  rintro ⟨g, h⟩
  have eL := pullbackEvenValue_comp_three u
    ((μ X Y).hom ⊗ₘ 𝟙 (F.obj Z)) (μ (X ⊗ Y) Z).hom (F.map (α_ X Y Z).hom) (g, h)
  have eR := pullbackEvenValue_comp_three u
    (α_ (F.obj X) (F.obj Y) (F.obj Z)).hom (𝟙 (F.obj X) ⊗ₘ (μ Y Z).hom)
    (μ X (Y ⊗ Z)).hom (g, h)
  apply eL.trans
  apply Eq.trans _ eR.symm
  dsimp only [μ, F, u]
  simp only [pullbackEvenValue_tensor, correctedReversedExteriorTensorIso_hom,
    reversedExteriorPairing_associator, pullbackEvenValue_associator,
    correctedReversedExteriorTensorIso_hom_family, pullbackEvenValue_id_family]
  have hh := correctedExteriorTensorator_associativity s t hl hr X.1 Y.1 Z.1 X.2 Y.2 Z.2 (g, h)
  dsimp only at hh
  rw [referenceProperty.comp_assoc] at hh
  with_unfolding_all exact hh

end RMod.BrundanEllis.Stacking
