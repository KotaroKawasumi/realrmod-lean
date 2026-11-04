import Superfusion.RMod.FromRawDCT.RealAssociatorNaturality
import Superfusion.RMod.RawDCT.RealComputableShiftedPentagonScalar
import Superfusion.RMod.RawDCT.RealPChiRouteBottom
import Superfusion.RMod.RawDCT.RealPChiRouteTop

/-!
# Pentagon for the finite-coordinate real associator

This concrete proof layer transports the already certified real fourfold
route equality to the finite-coordinate associator extracted from the
computably shifted raw DCT.  The proof reads the saved connector and fusion
coefficients through their public coordinate bridges; it does not evaluate a
fourfold route table again.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace RealAssociatorPentagon

/-! ## Fixed concrete data -/

private abbrev shiftedReal : RawDCTData :=
  realComputableShiftedRawDCT.data

private abbrev rawReal : RawDCTData :=
  realRawDCT.data

private abbrev tensorObj := Tensor.obj shiftedReal.D shiftedReal.C

/-- The proof layer views each stored coefficient algebra through the
additive group certified by its raw laws.  This is used only to simplify
finite sums of support-zero route entries. -/
@[implicit_reducible]
private def coefficientAddCommGroup (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) : AddCommGroup d.carrier where
  add := d.add
  add_assoc := h.add_assoc
  zero := d.zero
  zero_add := h.zero_add
  add_zero := h.add_zero
  neg := d.neg
  neg_add_cancel := h.neg_add
  add_comm := h.add_comm
  sub := fun x y => d.add x (d.neg y)
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

private instance coefficientAddCommGroupInstance
    (d : SuperAlgebraData ℝ) [h : Fact (SuperAlgebraLaws d)] :
    AddCommGroup d.carrier := coefficientAddCommGroup d h.out

/-- The zero of the proof-layer additive group is definitionally the zero
stored in the executable algebra data. -/
@[simp] private theorem coefficient_zero_eq_zero
    (d : SuperAlgebraData ℝ) [Fact (SuperAlgebraLaws d)] :
    d.zero = (0 : d.carrier) := rfl

/-- Natural multiples of the stored additive zero remain zero.  This is the
scalar form left after a finite route sum has been collapsed to support-zero
entries. -/
@[simp] private theorem coefficient_nsmul_zero
    (d : SuperAlgebraData ℝ) [Fact (SuperAlgebraLaws d)] (n : ℕ) :
    n • d.zero = d.zero := by
  change n • (0 : d.carrier) = 0
  exact nsmul_zero n

/-- Multiplication in the multiplicative wrapper is addition of the stored
labels.  Keeping this local normalization lemma avoids unfolding the wrapper
throughout the parity and scalar ledgers. -/
private theorem ofAdd_mul_eq (a b : ZMod 8) :
    Multiplicative.ofAdd a * Multiplicative.ofAdd b =
      Multiplicative.ofAdd (a + b) := rfl

/-! ## Endpoint-normalized route entries -/

private theorem cast_smul (dD : DData) {s t : ZMod 8}
    (h : s = t) (r : ℝ) (u : (dD.algebra s).carrier) :
    cast (congrArg (fun q : ZMod 8 => (dD.algebra q).carrier) h)
        ((dD.algebra s).smul r u) =
      (dD.algebra t).smul r
        (cast (congrArg (fun q : ZMod 8 => (dD.algebra q).carrier) h) u) := by
  subst t
  rfl

/-- An identity matrix entry transported from equal object positions to any
chosen representative of their common label is the stored algebra unit. -/
private theorem cast_homId_coeff (dD : DData) (X : Obj)
    (i j : Fin X.size) (hij : i = j)
    (hLabel : (X.atom i).label = (X.atom j).label)
    (t : ZMod 8) (hTotal : (X.atom i).label = t) :
    cast (congrArg (fun q : ZMod 8 => (dD.algebra q).carrier) hTotal)
        (((Hom.id dD X) i j).coeff hLabel) =
      (dD.algebra t).one := by
  subst j
  subst t
  have hpLabel : hLabel = rfl := Subsingleton.elim _ _
  cases hpLabel
  simp [Hom.id]

/-- Forward transport cancels the backward transport along the same algebra
label equality. -/
private theorem cast_algebra_symm_cancel (dD : DData) {a b : ZMod 8}
    (h : a = b) (u : (dD.algebra b).carrier) :
    cast (congrArg (fun q : ZMod 8 => (dD.algebra q).carrier) h)
        (cast (congrArg
          (fun q : ZMod 8 => (dD.algebra q).carrier) h.symm) u) = u := by
  subst b
  rfl

private theorem cast_cast_route {A B C : Type} (hAB : A = B)
    (hBC : B = C) (u : A) :
    cast hBC (cast hAB u) = cast (hAB.trans hBC) u := by
  subst B
  subst C
  rfl

/-- The preceding route-entry formula after transporting both endpoint
slots to any chosen representative of their common total label. -/
private theorem cast_normalizedHomEntry_route_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label))
    (t : ZMod 8)
    (hTotal : (X.atom i).label + (Y.atom j).label + (Z.atom k).label = t) :
    let qL := RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc
    let qR := RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc
    let hL := RealAssociatorLaws.leftRouteSlot_label X Y Z i j k ab abc
    let hR := RealAssociatorLaws.rightRouteSlot_label X Y Z i j k bc a_bc
    cast (congrArg
        (fun s : ZMod 8 => (shiftedReal.D.algebra s).carrier)
        (hL.trans hTotal))
        ((RealAssociator.homEntry X Y Z qL qR).coeff
          ((hL.trans hTotal).trans (hR.trans
            ((_root_.add_assoc (X.atom i).label (Y.atom j).label
              (Z.atom k).label).symm.trans hTotal)).symm)) =
      cast (congrArg
          (fun s : ZMod 8 => (shiftedReal.D.algebra s).carrier) hTotal)
        ((shiftedReal.D.algebra
          ((X.atom i).label + (Y.atom j).label + (Z.atom k).label)).smul
          (RawDCT.paritySign
            (shiftedReal.C.rowParity
              (X.atom i).label (Y.atom j).label ab * (Z.atom k).shift))
          (Associator.homCoefficient shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            ab abc bc a_bc)) := by
  dsimp only
  let hL := RealAssociatorLaws.leftRouteSlot_label X Y Z i j k ab abc
  let hR := RealAssociatorLaws.rightRouteSlot_label X Y Z i j k bc a_bc
  let hLR := RealAssociatorLaws.routeAssocLabelEq X Y Z
    i j k ab abc bc a_bc
  have hp :
      (hL.trans hTotal).trans
          (hR.trans ((_root_.add_assoc (X.atom i).label (Y.atom j).label
            (Z.atom k).label).symm.trans hTotal)).symm = hLR :=
    Subsingleton.elim _ _
  rw [show (RealAssociator.homEntry X Y Z
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc)
      (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc)).coeff
        ((hL.trans hTotal).trans
          (hR.trans ((_root_.add_assoc (X.atom i).label (Y.atom j).label
            (Z.atom k).label).symm.trans hTotal)).symm) =
      (RealAssociator.homEntry X Y Z
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc)
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc)).coeff hLR by
          exact congrArg (fun h => (RealAssociator.homEntry X Y Z
            (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc)
            (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc)).coeff h) hp]
  rw [RealAssociatorNaturality.realHomEntry_route_coeff]
  rw [cast_cast_route]

/-- A connector coefficient transported to a fixed total label is unchanged
when its source and target slots are replaced by equal slots.  Abstracting
the endpoint proofs here keeps dependent slot rewrites out of the concrete
four-object bookkeeping below. -/
private theorem cast_homEntry_coeff_of_slots_eq (X Y Z : Obj)
    (qL qL' : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj X Y) Z)
    (qR qR' : Tensor.Slot shiftedReal.D shiftedReal.C
      X (tensorObj Y Z))
    (hqL : qL = qL') (hqR : qR = qR')
    (t : ZMod 8)
    (hL : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj X Y) Z qL).label = t)
    (hR : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      X (tensorObj Y Z) qR).label = t)
    (hL' : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj X Y) Z qL').label = t)
    (hR' : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      X (tensorObj Y Z) qR').label = t) :
    cast (congrArg
        (fun s : ZMod 8 => (shiftedReal.D.algebra s).carrier) hL)
        ((RealAssociator.homEntry X Y Z qL qR).coeff
          (hL.trans hR.symm)) =
      cast (congrArg
          (fun s : ZMod 8 => (shiftedReal.D.algebra s).carrier) hL')
        ((RealAssociator.homEntry X Y Z qL' qR').coeff
          (hL'.trans hR'.symm)) := by
  subst qL'
  subst qR'
  rw [Subsingleton.elim hL hL', Subsingleton.elim hR hR']

/-- Once the two component labels are fixed, a tensor entry is the stored
binary coefficient with the target fusion row transported back to the source
labels.  This is the local form of the lowering lemma used by the existing
associator-naturality proof. -/
private theorem tensorEntry_coeff_of_label_eq
    {X X' Y Y' : Obj}
    (f : Hom shiftedReal.D X X')
    (g : Hom shiftedReal.D Y Y')
    (q : Tensor.Slot shiftedReal.D shiftedReal.C X Y)
    (q' : Tensor.Slot shiftedReal.D shiftedReal.C X' Y')
    (hA : (X.atom q.left).label = (X'.atom q'.left).label)
    (hB : (Y.atom q.right).label = (Y'.atom q'.right).label)
    (hQ : (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y q).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X' Y' q').label) :
    (Tensor.entry shiftedReal.D shiftedReal.C f g q q').coeff hQ =
      Tensor.coefficient shiftedReal.D shiftedReal.C
        (X.atom q.left).label (Y.atom q.right).label
        (X.atom q.left).shift (Y.atom q.right).shift
        (Y'.atom q'.right).shift q.fusion
        (Associator.castIndex shiftedReal hA.symm hB.symm q'.fusion)
        ((f q.left q'.left).coeff hA)
        ((g q.right q'.right).coeff hB) := by
  simp [Tensor.entry, hA, hB, Associator.castIndex]

/-- Transporting the right input label through a binary tensor coefficient
only transports its two fusion rows and its right algebra input. -/
private theorem tensorCoefficient_cast_right_label
    (a b b' : ZMod 8) (h : b = b') (s t t' : ZMod 2)
    (source target : shiftedReal.C.Index a b)
    (u : (shiftedReal.D.algebra a).carrier)
    (v : (shiftedReal.D.algebra b).carrier) :
    cast
        (congrArg (fun z : ZMod 8 => (shiftedReal.D.algebra z).carrier)
          (congrArg (fun z : ZMod 8 => a + z) h))
        (Tensor.coefficient shiftedReal.D shiftedReal.C
          a b s t t' source target u v) =
      Tensor.coefficient shiftedReal.D shiftedReal.C a b' s t t'
        (Associator.castIndex shiftedReal rfl h source)
        (Associator.castIndex shiftedReal rfl h target) u
        (cast (congrArg
          (fun z : ZMod 8 => (shiftedReal.D.algebra z).carrier) h) v) := by
  subst b'
  rfl

/-- Transporting the left input label through a binary tensor coefficient
only transports its two fusion rows and its left algebra input. -/
private theorem tensorCoefficient_cast_left_label
    (a a' b : ZMod 8) (h : a = a') (s t t' : ZMod 2)
    (source target : shiftedReal.C.Index a b)
    (u : (shiftedReal.D.algebra a).carrier)
    (v : (shiftedReal.D.algebra b).carrier) :
    cast
        (congrArg (fun z : ZMod 8 => (shiftedReal.D.algebra z).carrier)
          (congrArg (fun z : ZMod 8 => z + b) h))
        (Tensor.coefficient shiftedReal.D shiftedReal.C
          a b s t t' source target u v) =
      Tensor.coefficient shiftedReal.D shiftedReal.C a' b s t t'
        (Associator.castIndex shiftedReal h rfl source)
        (Associator.castIndex shiftedReal h rfl target)
        (cast (congrArg
          (fun z : ZMod 8 => (shiftedReal.D.algebra z).carrier) h) u) v := by
  subst a'
  rfl

/-! ## Shifted connector coefficients

The first bridge below will identify a shifted connector matrix coefficient
with the corresponding raw coefficient multiplied by its two diagonal frame
signs and the stored `beta⁻¹` scalar.  It is kept separate from the later
four-object bookkeeping so the latter never unfolds the connector table.
-/

/-- Reading one coefficient of the shifted connector introduces exactly the
source and target frame signs and the stored `beta⁻¹` rescaling. -/
theorem realShiftedHomCoefficient_eq
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c)) :
    Associator.homCoefficient shiftedReal a b c
        sourceAB sourceABC targetBC targetABC =
      (shiftedReal.D.algebra (a + b + c)).smul
        (rightRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c targetBC *
          (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
          leftRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c sourceAB)
        (Associator.homCoefficient rawReal a b c
          sourceAB sourceABC targetBC targetABC) := by
  let q : ℝ := leftRouteFrameSign rawReal.C realComputableNuBeta.data
    a b c sourceAB
  have hframe :
      leftRouteFrameInv rawReal.D rawReal.C realComputableNuBeta.data
          a b c (Associator.leftDelta shiftedReal a b c
            sourceAB sourceABC) =
        fun targetAB targetABC =>
          (rawReal.D.algebra (a + b + c)).smul q
            (Associator.leftDelta rawReal a b c sourceAB sourceABC
              targetAB targetABC) := by
    funext targetAB targetABC
    change
      (rawReal.D.algebra (a + b + c)).smul
          (leftRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c targetAB)
          (if targetAB = sourceAB then
            if targetABC = sourceABC then
              (rawReal.D.algebra (a + b + c)).one
            else (rawReal.D.algebra (a + b + c)).zero
          else (rawReal.D.algebra (a + b + c)).zero) =
        (rawReal.D.algebra (a + b + c)).smul q
          (if targetAB = sourceAB then
            if targetABC = sourceABC then
              (rawReal.D.algebra (a + b + c)).one
            else (rawReal.D.algebra (a + b + c)).zero
          else (rawReal.D.algebra (a + b + c)).zero)
    by_cases hAB : targetAB = sourceAB
    · subst targetAB
      by_cases hABC : targetABC = sourceABC
      · subst targetABC
        simp [q]
      · simp [hABC, q,
          (realRawDCT.laws.D.algebra_laws _).smul_zero]
    · simp [hAB, q,
        (realRawDCT.laws.D.algebra_laws _).smul_zero]
  have hofCoord :
      rawReal.T.leftOfCoord a b c
          (fun targetAB targetABC =>
            (rawReal.D.algebra (a + b + c)).smul q
              (Associator.leftDelta rawReal a b c sourceAB sourceABC
                targetAB targetABC)) =
        rawReal.T.leftRoute.smul a b c q
          (rawReal.T.leftOfCoord a b c
            (Associator.leftDelta rawReal a b c sourceAB sourceABC)) := by
    calc
      _ = rawReal.T.leftOfCoord a b c
          (rawReal.T.leftToCoord a b c
            (rawReal.T.leftRoute.smul a b c q
              (rawReal.T.leftOfCoord a b c
                (Associator.leftDelta rawReal a b c
                  sourceAB sourceABC)))) := by
            congr 1
      _ = _ := realRawDCT.laws.T.left_ofCoord_toCoord _ _ _ _
  unfold Associator.homCoefficient shiftedReal rawReal
  change
    rightRouteFrame rawReal.D rawReal.C realComputableNuBeta.data a b c
        (rawReal.T.rightToCoord a b c
          (rawReal.T.rightRoute.smul a b c
            (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ)
            (rawReal.T.hom a b c
              (rawReal.T.leftOfCoord a b c
                (leftRouteFrameInv rawReal.D rawReal.C
                  realComputableNuBeta.data a b c
                  (Associator.leftDelta shiftedReal a b c
                    sourceAB sourceABC))))))
      targetBC targetABC = _
  rw [hframe, hofCoord, realRawDCT.laws.T.hom_smul]
  rw [realRawDCT.laws.T.right_toCoord_smul,
    realRawDCT.laws.T.right_toCoord_smul]
  unfold rightRouteFrame
  simp only [q]
  rw [← (realRawDCT.laws.D.algebra_laws _).smul_assoc,
    ← (realRawDCT.laws.D.algebra_laws _).smul_assoc]
  congr 1

/-! ## Frozen connector table entry -/

/-- A raw connector coefficient extracted by `Associator.homCoefficient` is
literally the saved forward table entry.  The two fixed-order sums collapse
against the delta vector; the table itself is not evaluated. -/
theorem realRawHomCoefficient_eq_forwardEntry
    (a b c : ZMod 8)
    (sourceAB : rawReal.C.Index a b)
    (sourceABC : rawReal.C.Index (a + b) c)
    (targetBC : rawReal.C.Index b c)
    (targetABC : rawReal.C.Index a (b + c)) :
    Associator.homCoefficient rawReal a b c
        sourceAB sourceABC targetBC targetABC =
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC := by
  change RModCoordinate.FusionTable.Index a b at sourceAB
  change RModCoordinate.FusionTable.Index (a + b) c at sourceABC
  change RModCoordinate.FusionTable.Index b c at targetBC
  change RModCoordinate.FusionTable.Index a (b + c) at targetABC
  unfold Associator.homCoefficient rawReal
  change realTHom a b c
      (Associator.leftDelta rawReal a b c sourceAB sourceABC)
        targetBC targetABC = _
  unfold realTHom CData.rawFinSum
  change (List.ofFn (fun sourceAB_1 =>
      (List.ofFn (fun sourceABC_1 =>
        RModCoordinate.Coeff.mul (a + b + c)
          (realTForwardEntry a b c targetBC targetABC
            sourceAB_1 sourceABC_1)
          (Associator.leftDelta rawReal a b c sourceAB sourceABC
            sourceAB_1 sourceABC_1))).sum)).sum = _
  rw [List.sum_ofFn]
  simp_rw [List.sum_ofFn]
  rw [Fintype.sum_eq_single sourceAB]
  · rw [Fintype.sum_eq_single sourceABC]
    · rw [Associator.leftDelta_source]
      change RModCoordinate.Coeff.mul (a + b + c)
          (realTForwardEntry a b c targetBC targetABC
            sourceAB sourceABC)
          (RModCoordinate.Coeff.one (a + b + c)) = _
      exact RModCoordinate.Coeff.mul_one _ _
    · intro other hne
      rw [show Associator.leftDelta rawReal a b c sourceAB sourceABC
          sourceAB other = (rawReal.D.algebra (a + b + c)).zero by
        exact Associator.leftDelta_off_second rawReal a b c
          sourceAB sourceABC other hne]
      change RModCoordinate.Coeff.mul (a + b + c)
          (realTForwardEntry a b c targetBC targetABC sourceAB other)
          (RModCoordinate.Coeff.zero (a + b + c)) = 0
      exact RModCoordinate.Coeff.mul_zero _ _
  · intro other hne
    apply Finset.sum_eq_zero
    intro sourceABC_1 _
    rw [show Associator.leftDelta rawReal a b c sourceAB sourceABC
        other sourceABC_1 = (rawReal.D.algebra (a + b + c)).zero by
      exact Associator.leftDelta_off_first rawReal a b c
        sourceAB other sourceABC sourceABC_1 hne]
    change RModCoordinate.Coeff.mul (a + b + c)
        (realTForwardEntry a b c targetBC targetABC other sourceABC_1)
        (RModCoordinate.Coeff.zero (a + b + c)) = 0
    exact RModCoordinate.Coeff.mul_zero _ _

/-- At a canonical coefficient basis coordinate, the shifted associator
coefficient is the saved integer connector kernel multiplied by the three
shift factors. -/
theorem realShiftedHomCoefficient_apply
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c))
    (targetBasis : Fin (RawDCT.RealPChiKernel.coefficientRank
      (a + b + c))) :
    Associator.homCoefficient shiftedReal a b c
        sourceAB sourceABC targetBC targetABC targetBasis =
      (rightRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c targetBC *
          (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
          leftRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c sourceAB) *
        ((RawDCT.RealPChiKernel.connectorLinearCoeff a b c
          targetBC.val targetABC.val sourceAB.val sourceABC.val
          targetBasis.val
          (RawDCT.RealPChiKernel.coefficientUnitIndex
            (a + b + c)).val : ℤ) : ℝ) := by
  change RModCoordinate.FusionTable.Index a b at sourceAB
  change RModCoordinate.FusionTable.Index (a + b) c at sourceABC
  change RModCoordinate.FusionTable.Index b c at targetBC
  change RModCoordinate.FusionTable.Index a (b + c) at targetABC
  rw [realShiftedHomCoefficient_eq,
    realRawHomCoefficient_eq_forwardEntry]
  change _ * realTForwardEntry a b c targetBC targetABC
      sourceAB sourceABC targetBasis = _
  have h := RawDCT.RealPChiKernel.connectorLinearCoeff_cast a b c
    (targetBC, targetABC) (sourceAB, sourceABC) targetBasis
    (RawDCT.RealPChiKernel.coefficientUnitIndex (a + b + c))
  rw [RawDCT.RealPChiRouteBridge.coefficientBasis_unit,
    RModCoordinate.Coeff.mul_one] at h
  rw [← h]

/-- Multiplying a canonical coefficient basis vector by one shifted
connector entry reads the same saved integer kernel at an arbitrary source
basis coordinate.  This is the compositional form used by the pentagon
routes; it still evaluates only one stored ternary connector. -/
theorem realShiftedHomCoefficient_mul_basis
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c))
    (sourceBasis targetBasis : Fin
      (RawDCT.RealPChiKernel.coefficientRank (a + b + c))) :
    (shiftedReal.D.algebra (a + b + c)).mul
        (Associator.homCoefficient shiftedReal a b c
          sourceAB sourceABC targetBC targetABC)
        (RawDCT.RealPChiKernel.coefficientBasis
          (a + b + c) sourceBasis) targetBasis =
      (rightRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c targetBC *
          (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
          leftRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c sourceAB) *
        ((RawDCT.RealPChiKernel.connectorLinearCoeff a b c
          targetBC.val targetABC.val sourceAB.val sourceABC.val
          targetBasis.val sourceBasis.val : ℤ) : ℝ) := by
  rw [realShiftedHomCoefficient_eq]
  rw [(realComputableShiftedRawDCT.laws.D.algebra_laws
    (a + b + c)).smul_mul]
  rw [realRawHomCoefficient_eq_forwardEntry]
  change _ * RModCoordinate.Coeff.mul (a + b + c)
      (realTForwardEntry a b c targetBC targetABC sourceAB sourceABC)
      (RawDCT.RealPChiKernel.coefficientBasis
        (a + b + c) sourceBasis) targetBasis = _
  rw [← RawDCT.RealPChiKernel.connectorLinearCoeff_cast
    a b c (targetBC, targetABC) (sourceAB, sourceABC)
      targetBasis sourceBasis]

/-! ## Four-object slot normal forms

The source and target of the pentagon are nested tensor-slot lists.  These
constructors name one canonical four-object block without unfolding either
list enumeration.  Their rows are precisely the `QuadSource` and
`QuadTarget` rows used by the saved integer kernel.
-/

/-- The left-associated four-object slot determined by three fusion rows. -/
def quadLeftSlot (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z := by
  let q := RealAssociatorLaws.leftRouteSlot W X Y i j k ab abc
  exact RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
    (tensorObj W X) Y Z
      ⟨q, l,
        Associator.castIndex shiftedReal
          (RealAssociatorLaws.leftRouteSlot_label W X Y
            i j k ab abc).symm rfl abcd⟩

@[simp] theorem quadLeftSlot_inner (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    (Tensor.slots shiftedReal.D shiftedReal.C (tensorObj W X) Y).get
        (quadLeftSlot W X Y Z i j k l ab abc abcd).left =
      RealAssociatorLaws.leftRouteSlot W X Y i j k ab abc := by
  unfold quadLeftSlot
  apply RealAssociatorLaws.leftSlotPack_inner

@[simp] theorem quadLeftSlot_right (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    (quadLeftSlot W X Y Z i j k l ab abc abcd).right = l := by
  unfold quadLeftSlot
  apply RealAssociatorLaws.leftSlotPack_right

@[simp] theorem quadLeftSlot_label (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z
      (quadLeftSlot W X Y Z i j k l ab abc abcd)).label =
        (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj W X) Y
      ((Tensor.slots shiftedReal.D shiftedReal.C (tensorObj W X) Y).get
        (quadLeftSlot W X Y Z i j k l ab abc abcd).left)).label +
      (Z.atom (quadLeftSlot W X Y Z i j k l ab abc abcd).right).label = _
  rw [quadLeftSlot_inner, quadLeftSlot_right]
  exact congrArg (fun a => a + (Z.atom l).label)
    (RealAssociatorLaws.leftRouteSlot_label W X Y i j k ab abc)

/-- The right-associated four-object slot determined by three fusion rows. -/
def quadRightSlot (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) := by
  let q := RealAssociatorLaws.rightRouteSlot X Y Z j k l cd bcd
  exact RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
    W X (tensorObj Y Z)
      ⟨i, q,
        Associator.castIndex shiftedReal rfl
          ((_root_.add_assoc _ _ _).trans
            (RealAssociatorLaws.rightRouteSlot_label X Y Z
              j k l cd bcd).symm)
          abcd⟩

@[simp] theorem quadRightSlot_left (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (quadRightSlot W X Y Z i j k l cd bcd abcd).left = i := by
  unfold quadRightSlot
  apply RealAssociatorLaws.rightSlotPack_left

@[simp] theorem quadRightSlot_inner (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (Tensor.slots shiftedReal.D shiftedReal.C X (tensorObj Y Z)).get
        (quadRightSlot W X Y Z i j k l cd bcd abcd).right =
      RealAssociatorLaws.rightRouteSlot X Y Z j k l cd bcd := by
  unfold quadRightSlot
  apply RealAssociatorLaws.rightSlotPack_inner

@[simp] theorem quadRightSlot_label (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))
      (quadRightSlot W X Y Z i j k l cd bcd abcd)).label =
        (W.atom i).label +
          ((X.atom j).label + ((Y.atom k).label + (Z.atom l).label)) := by
  change (W.atom (quadRightSlot W X Y Z i j k l cd bcd abcd).left).label +
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X (tensorObj Y Z)
        ((Tensor.slots shiftedReal.D shiftedReal.C X (tensorObj Y Z)).get
          (quadRightSlot W X Y Z i j k l cd bcd abcd).right)).label = _
  rw [quadRightSlot_left, quadRightSlot_inner]
  exact congrArg (fun a => (W.atom i).label + a)
    (RealAssociatorLaws.rightRouteSlot_label X Y Z j k l cd bcd)

private theorem castIndex_symm_cancel {a b a' b' : ZMod 8}
    (ha : a = a') (hb : b = b') (r : shiftedReal.C.Index a b) :
    Associator.castIndex shiftedReal ha.symm hb.symm
      (Associator.castIndex shiftedReal ha hb r) = r := by
  subst a'
  subst b'
  rfl

/-- Transport of a fusion row changes only its endpoint types, not the
stored finite row number. -/
@[simp] private theorem castIndex_val
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : shiftedReal.C.Index a b) :
    (Associator.castIndex shiftedReal ha hb r).val = r.val := by
  subst a'
  subst b'
  rfl

/-- Row parity is invariant under transport of the two endpoint labels. -/
@[simp] private theorem rowParity_castIndex
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : shiftedReal.C.Index a b) :
    shiftedReal.C.rowParity a' b'
        (Associator.castIndex shiftedReal ha hb r) =
      shiftedReal.C.rowParity a b r := by
  subst a'
  subst b'
  rfl

/-- The actual connector coefficient commutes with simultaneous transport
of its three labels and four fusion rows. -/
private theorem homCoefficient_transport
    {a b c a' b' c' : ZMod 8}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (ab : shiftedReal.C.Index a b)
    (abc : shiftedReal.C.Index (a + b) c)
    (bc : shiftedReal.C.Index b c)
    (a_bc : shiftedReal.C.Index a (b + c)) :
    Associator.homCoefficient shiftedReal a b c ab abc bc a_bc =
      cast
        (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          (congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc)).symm
        (Associator.homCoefficient shiftedReal a' b' c'
          (Associator.castIndex shiftedReal ha hb ab)
          (Associator.castIndex shiftedReal
            (congrArg₂ (· + ·) ha hb) hc abc)
          (Associator.castIndex shiftedReal hb hc bc)
          (Associator.castIndex shiftedReal ha
            (congrArg₂ (· + ·) hb hc) a_bc)) := by
  subst a'
  subst b'
  subst c'
  rfl

/-- Specializing the preceding transport to the first endpoint cancels the
backward row transports after the coefficient itself is moved forward. -/
private theorem cast_homCoefficient_first_label
    {a a' b c : ZMod 8} (ha : a = a')
    (ab : shiftedReal.C.Index a' b)
    (abc : shiftedReal.C.Index (a' + b) c)
    (bc : shiftedReal.C.Index b c)
    (a_bc : shiftedReal.C.Index a' (b + c)) :
    cast
        (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          (congrArg (fun q => q + b + c) ha))
        (Associator.homCoefficient shiftedReal a b c
          (Associator.castIndex shiftedReal ha.symm rfl ab)
          (Associator.castIndex shiftedReal
            (congrArg (fun q => q + b) ha).symm rfl abc)
          bc
          (Associator.castIndex shiftedReal ha.symm rfl a_bc)) =
      Associator.homCoefficient shiftedReal a' b c ab abc bc a_bc := by
  subst a'
  rfl

/-- The same transport cancellation when only the middle connector label is
changed.  All four row indices move functorially with that label. -/
private theorem cast_homCoefficient_second_label
    {a b b' c : ZMod 8} (hb : b = b')
    (ab : shiftedReal.C.Index a b')
    (abc : shiftedReal.C.Index (a + b') c)
    (bc : shiftedReal.C.Index b' c)
    (a_bc : shiftedReal.C.Index a (b' + c)) :
    cast
        (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          (congrArg (fun q => a + q + c) hb))
        (Associator.homCoefficient shiftedReal a b c
          (Associator.castIndex shiftedReal rfl hb.symm ab)
          (Associator.castIndex shiftedReal
            (congrArg (fun q => a + q) hb).symm rfl abc)
          (Associator.castIndex shiftedReal hb.symm rfl bc)
          (Associator.castIndex shiftedReal rfl
            (congrArg (fun q => q + c) hb).symm a_bc)) =
      Associator.homCoefficient shiftedReal a b' c ab abc bc a_bc := by
  subst b'
  rfl

/-- The analogous cancellation when only the third connector label is
transported. -/
private theorem cast_homCoefficient_third_label
    {a b c c' : ZMod 8} (hc : c = c')
    (ab : shiftedReal.C.Index a b)
    (abc : shiftedReal.C.Index (a + b) c')
    (bc : shiftedReal.C.Index b c')
    (a_bc : shiftedReal.C.Index a (b + c')) :
    cast
        (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          (congrArg (fun q => a + b + q) hc))
        (Associator.homCoefficient shiftedReal a b c ab
          (Associator.castIndex shiftedReal rfl hc.symm abc)
          (Associator.castIndex shiftedReal rfl hc.symm bc)
          (Associator.castIndex shiftedReal rfl
            (congrArg (fun q => b + q) hc).symm a_bc)) =
      Associator.homCoefficient shiftedReal a b c' ab abc bc a_bc := by
  subst c'
  rfl

/-- Transporting a stored row in two stages agrees with transport along
the composite endpoint equalities. -/
private theorem castIndex_trans
    {a b a' b' a'' b'' : ZMod 8}
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (r : shiftedReal.C.Index a b) :
    Associator.castIndex shiftedReal ha' hb'
        (Associator.castIndex shiftedReal ha hb r) =
      Associator.castIndex shiftedReal (ha.trans ha') (hb.trans hb') r := by
  subst a'
  subst b'
  subst a''
  subst b''
  rfl

/-- Row transport is independent of the chosen equality proofs. -/
private theorem castIndex_proof_irrel
    {a b a' b' : ZMod 8}
    (ha ha' : a = a') (hb hb' : b = b')
    (r : shiftedReal.C.Index a b) :
    Associator.castIndex shiftedReal ha hb r =
      Associator.castIndex shiftedReal ha' hb' r := by
  subst a'
  subst b'
  rfl

/-- Transporting fusion rows along fixed endpoint equalities is injective. -/
private theorem castIndex_injective
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b') :
    Function.Injective (Associator.castIndex shiftedReal ha hb) := by
  subst a'
  subst b'
  exact fun _ _ h => h

/-- Every source slot of the pentagon has one explicit four-object normal
form.  This only reindexes the canonical slot list. -/
theorem exists_eq_quadLeftSlot (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z) :
    ∃ (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size)
      (l : Fin Z.size)
      (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
      (abc : shiftedReal.C.Index
        ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
      (abcd : shiftedReal.C.Index
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
        (Z.atom l).label),
      q = quadLeftSlot W X Y Z i j k l ab abc abcd := by
  let c := (RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
    (tensorObj W X) Y Z).symm q
  have hrecover := (RealAssociatorLaws.leftSlotPack
    shiftedReal.D shiftedReal.C (tensorObj W X) Y Z).apply_symm_apply q
  rcases hc : c with ⟨qInner, l, outer⟩
  rcases RealAssociatorLaws.exists_eq_leftRouteSlot W X Y qInner with
    ⟨i, j, k, ab, abc, hInner⟩
  subst qInner
  let hLabel := RealAssociatorLaws.leftRouteSlot_label
    W X Y i j k ab abc
  let abcd := Associator.castIndex shiftedReal hLabel rfl outer
  refine ⟨i, j, k, l, ab, abc, abcd, ?_⟩
  have hc' : c = ⟨RealAssociatorLaws.leftRouteSlot W X Y
      i j k ab abc, l, outer⟩ := hc
  calc
    q = RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
        (tensorObj W X) Y Z
        ⟨RealAssociatorLaws.leftRouteSlot W X Y i j k ab abc,
          l, outer⟩ := by rw [← hc', hrecover]
    _ = quadLeftSlot W X Y Z i j k l ab abc abcd := by
      unfold quadLeftSlot
      dsimp only [hLabel, abcd]
      rw [castIndex_symm_cancel]

/-- Every target slot has one explicit four-object normal form, with its
outer row transported to the left-associated label used by `QuadTarget`. -/
theorem exists_eq_quadRightSlot (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))) :
    ∃ (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size)
      (l : Fin Z.size)
      (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
      (bcd : shiftedReal.C.Index (X.atom j).label
        ((Y.atom k).label + (Z.atom l).label))
      (abcd : shiftedReal.C.Index (W.atom i).label
        ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)),
      q = quadRightSlot W X Y Z i j k l cd bcd abcd := by
  let c := (RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
    W X (tensorObj Y Z)).symm q
  have hrecover := (RealAssociatorLaws.rightSlotPack
    shiftedReal.D shiftedReal.C W X (tensorObj Y Z)).apply_symm_apply q
  rcases hc : c with ⟨i, qInner, outer⟩
  rcases RealAssociatorLaws.exists_eq_rightRouteSlot X Y Z qInner with
    ⟨j, k, l, cd, bcd, hInner⟩
  subst qInner
  let hLabel := (RealAssociatorLaws.rightRouteSlot_label X Y Z
    j k l cd bcd).trans (_root_.add_assoc _ _ _).symm
  let abcd := Associator.castIndex shiftedReal rfl hLabel outer
  refine ⟨i, j, k, l, cd, bcd, abcd, ?_⟩
  have hc' : c = ⟨i, RealAssociatorLaws.rightRouteSlot X Y Z
      j k l cd bcd, outer⟩ := hc
  calc
    q = RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W X (tensorObj Y Z)
        ⟨i, RealAssociatorLaws.rightRouteSlot X Y Z j k l cd bcd,
          outer⟩ := by rw [← hc', hrecover]
    _ = quadRightSlot W X Y Z i j k l cd bcd abcd := by
      unfold quadRightSlot
      dsimp only [hLabel, abcd]
      rw [castIndex_symm_cancel]

/-! ## Endpoint-sign ledger

The five normalized associator entries contribute one sign at each left
endpoint.  Comparing the three-edge and two-edge products leaves precisely
the sign below.  The first summand is the degree crossed by the outer right
whiskering; the second is the binary-row interchange term.  This finite
identity is independent of every connector and fourfold route table.
-/

/-- The executable integer sign in the frozen fourfold kernel is the same
real parity sign used by the shifted coordinate construction. -/
private theorem cast_koszulSign_eq_paritySign (p q : ZMod 2) :
    ((RawDCT.RealPChiKernel.koszulSign (p.val * q.val) : ℤ) : ℝ) =
      RawDCT.paritySign (p * q) := by
  rcases zmod2_cases p with rfl | rfl <;>
    rcases zmod2_cases q with rfl | rfl <;>
      norm_num [RawDCT.RealPChiKernel.koszulSign, RawDCT.paritySign,
        ZMod.val_one]

/-- The unit-valued sign in the generic shift scalar has the same real
value as the coefficient-algebra parity sign. -/
private theorem coe_sgn_eq_paritySign (p : ZMod 2) :
    (((Superfusion.sgn p : ℝˣ) : ℝ)) = RawDCT.paritySign p := by
  rcases zmod2_cases p with rfl | rfl <;>
    simp [Superfusion.sgn, RawDCT.paritySign]

/-- The saved pair of bottom-route integer signs is the same pair of real
parity signs.  The nontrivial natural-number sum in the second exponent is
handled by the existing semantic bottom-sign theorem. -/
private theorem cast_bottomKoszulSigns_eq_paritySigns
    (p q r s : ZMod 2) :
    ((RawDCT.RealPChiKernel.koszulSign
        (p.val * q.val) : ℤ) : ℝ) *
      ((RawDCT.RealPChiKernel.koszulSign
        (r.val * (s.val + q.val)) : ℤ) : ℝ) =
      RawDCT.paritySign (p * q) *
        RawDCT.paritySign (r * (s + q)) := by
  have h := RawDCT.RealPChiRouteBottom.semanticBottomSign_eq_koszulSigns
    p q r s
  push_cast at h
  rw [← h]
  have htwo : (2 : ZMod 2) = 0 := by decide
  rcases zmod2_cases p with rfl | rfl <;>
    rcases zmod2_cases q with rfl | rfl <;>
      rcases zmod2_cases r with rfl | rfl <;>
        rcases zmod2_cases s with rfl | rfl <;>
          norm_num [Superfusion.sgn, RawDCT.paritySign,
            RawDCT.RealPChiKernel.koszulSign, htwo]
  all_goals simp only [if_pos htwo] <;> norm_num

/-- Square form of the existing parity-sign involution theorem. -/
@[simp] private theorem paritySign_sq (p : ZMod 2) :
    RawDCT.paritySign p ^ 2 = 1 := by
  simpa only [pow_two] using RawDCT.shiftParitySign_mul_self p

/-! ### Complete scalar ledger

The next two exponents collect only the scalars which surround the saved
connector and fusion coefficients.  Besides the three endpoint signs they
include the raw-to-shifted route-frame signs.  The two final terms of the
top exponent are the left and right whiskering twists.  No table value
occurs in either definition.
-/

private def topCoordinateExponent
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
      nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
      P1 P3 : ZMod 2) : ZMod 2 :=
  -- Endpoint normalizations of the three top associators.
  (pAB + nAB) * sY +
  (pA_BC + nA_BC) * sZ +
  (pBC + nBC) * sZ +
  -- Source/target frame signs of the three shifted connectors.
  nA_BC * pBC + nAB_C * pAB +
  nA_BCD * pBC_D + nABC_D * pA_BC +
  nB_CD * pCD + nBC_D * pBC +
  -- Whiskering the first and third connector coefficients.
  (sZ + nABC_D) * (P1 + pAB + pABC + pBC + pA_BC) +
  nA_BCD * (P3 + pBC + pBC_D + pCD + pBCD)

private def bottomCoordinateExponent
    (sY sZ pAB pABC pCD pBCD
      nAB nCD nAB_C nABC_D nAB_CD nA_BCD : ZMod 2) : ZMod 2 :=
  -- Endpoint normalizations of the two bottom associators.
  (pABC + nAB_C) * sZ +
  (pAB + nAB) * (sY + sZ + pCD + nCD) +
  -- Source/target frame signs of the two shifted connectors.
  nAB_CD * pCD + nABC_D * pABC +
  nA_BCD * pBCD + nAB_CD * pAB

/-- The eleven separate signs occurring along the three top edges multiply
to the single exponent used by the common-sign ledger. -/
private theorem topCoordinateParityProduct_eq
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
      nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
      P1 P3 : ZMod 2) :
    RawDCT.paritySign ((pAB + nAB) * sY) *
      RawDCT.paritySign ((pA_BC + nA_BC) * sZ) *
      RawDCT.paritySign ((pBC + nBC) * sZ) *
      RawDCT.paritySign (nA_BC * pBC) *
      RawDCT.paritySign (nAB_C * pAB) *
      RawDCT.paritySign (nA_BCD * pBC_D) *
      RawDCT.paritySign (nABC_D * pA_BC) *
      RawDCT.paritySign (nB_CD * pCD) *
      RawDCT.paritySign (nBC_D * pBC) *
      RawDCT.paritySign
        ((sZ + nABC_D) * (P1 + pAB + pABC + pBC + pA_BC)) *
      RawDCT.paritySign
        (nA_BCD * (P3 + pBC + pBC_D + pCD + pBCD)) =
      RawDCT.paritySign
        (topCoordinateExponent
          sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
          nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
          P1 P3) := by
  simp only [← shiftParitySign_add]
  unfold topCoordinateExponent
  congr 1

/-- The six signs surrounding the two bottom connector entries are exactly
the bottom coordinate exponent.  This is parity bookkeeping only; it does
not inspect either connector table. -/
private theorem bottomCoordinateParityProduct_eq
    (sY sZ pAB pABC pCD pBCD
      nAB nCD nAB_C nABC_D nAB_CD nA_BCD : ZMod 2) :
    RawDCT.paritySign (pABC * sZ + nAB_C * sZ) *
      RawDCT.paritySign (nAB_CD * pCD) *
      RawDCT.paritySign (nABC_D * pABC) *
      RawDCT.paritySign
        (sZ * pAB + sZ * nAB + pAB * sY + pAB * pCD + pAB * nCD +
          nAB * sY + nAB * pCD + nAB * nCD) *
      RawDCT.paritySign (nA_BCD * pBCD) *
      RawDCT.paritySign (nAB_CD * pAB) =
        RawDCT.paritySign
          (bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
            nAB nCD nAB_C nABC_D nAB_CD nA_BCD) := by
  simp only [← shiftParitySign_add]
  unfold bottomCoordinateExponent
  congr 1
  ring

/-- Full parity bookkeeping for one four-object coordinate.

The right side is exactly, in order, the top shift degree, the saved top
Koszul sign, the bottom shift degree, and the two saved bottom Koszul signs.
Thus the categorical endpoint/frame/whisker normalizations differ by the
same scalar already used by the executable fourfold kernel. -/
private theorem coordinateExponent_top_add_bottom
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
      nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
      P1 P2 P3 P4 P5 : ZMod 2)
    (hP1 : P1 = nAB + nAB_C + nBC + nA_BC)
    (hP2 : P2 = nA_BC + nABC_D + nBC_D + nA_BCD)
    (hP3 : P3 = nBC + nBC_D + nCD + nB_CD)
    (hP4 : P4 = nAB_C + nABC_D + nCD + nAB_CD)
    (hP5 : P5 = nAB + nAB_CD + nB_CD + nA_BCD) :
    topCoordinateExponent
        sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
        nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
        P1 P3 +
      bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
        nAB nCD nAB_C nABC_D nAB_CD nA_BCD =
      (nABC_D * P1 + nA_BCD * P3) + P2 * pBC +
        nAB * nCD + (P4 * pAB + pCD * (P5 + pAB)) := by
  rw [hP1, hP2, hP3, hP4, hP5]
  unfold topCoordinateExponent bottomCoordinateExponent
  ring_nf
  rw [show (2 : ZMod 2) = 0 by decide]
  ring

/-- Equivalently, after multiplying each route by its own shift and saved
kernel signs, both routes carry one common endpoint exponent. -/
private theorem coordinateCommonExponent_eq
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
      nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
      P1 P2 P3 P4 P5 : ZMod 2)
    (hP1 : P1 = nAB + nAB_C + nBC + nA_BC)
    (hP2 : P2 = nA_BC + nABC_D + nBC_D + nA_BCD)
    (hP3 : P3 = nBC + nBC_D + nCD + nB_CD)
    (hP4 : P4 = nAB_C + nABC_D + nCD + nAB_CD)
    (hP5 : P5 = nAB + nAB_CD + nB_CD + nA_BCD) :
    topCoordinateExponent
        sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
        nAB nBC nCD nAB_C nA_BC nABC_D nBC_D nB_CD nAB_CD nA_BCD
        P1 P3 + (nABC_D * P1 + nA_BCD * P3 + P2 * pBC) =
      bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
          nAB nCD nAB_C nABC_D nAB_CD nA_BCD +
        (nAB * nCD + P4 * pAB + pCD * (P5 + pAB)) := by
  rw [hP1, hP2, hP3, hP4, hP5]
  unfold topCoordinateExponent bottomCoordinateExponent
  ring_nf
  rw [show (2 : ZMod 2) = 0 by decide]
  ring

/-- The computable parity trivialization writes every raw connector degree
as the four adjacent values of `nu`. -/
private theorem realRawParity_eq_shiftNu_sum (a b c : ZMod 8) :
    rawReal.T.parity a b c =
      shiftNu realComputableNuBeta.data a b +
      shiftNu realComputableNuBeta.data (a + b) c +
      shiftNu realComputableNuBeta.data b c +
      shiftNu realComputableNuBeta.data a (b + c) := by
  have h := realComputableNuBeta.laws.parity
    (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
      (Multiplicative.ofAdd c)
  change Superfusion.d₂ realComputableNuBeta.data.nu
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) = rawReal.T.parity a b c at h
  rw [← h]
  simp only [Superfusion.d₂, shiftNu, ZModModule.sub_eq_add,
    ofAdd_mul_eq]
  ac_rfl

/-- A shifted fusion-row index carries the same finite row data as the raw
table.  This named cast prevents later tactics from unfolding the whole shift
construction merely to read a saved row parity. -/
private def rawIndexOfShifted (a b : ZMod 8)
    (r : shiftedReal.C.Index a b) : rawReal.C.Index a b :=
  cast (show shiftedReal.C.Index a b = rawReal.C.Index a b from rfl) r

/-- Read the saved raw row parity at a shifted row index. -/
private def rawRowParityOfShifted (a b : ZMod 8)
    (r : shiftedReal.C.Index a b) : ZMod 2 :=
  rawReal.C.rowParity a b (rawIndexOfShifted a b r)

/-- The natural row bit stored in the executable kernel is the value of the
same unchanged raw row parity viewed through a shifted row index. -/
private theorem rowParityNat_eq_rawRowParityOfShifted_val
    (a b : ZMod 8) (r : shiftedReal.C.Index a b) :
    RawDCT.RealPChiKernel.rowParityNat a b r.val =
      (rawRowParityOfShifted a b r).val := by
  change RModCoordinate.FusionTable.Index a b at r
  change RawDCT.RealPChiKernel.rowParityNat a b r.val =
    (RModCoordinate.FusionTable.indexParity a b r).val
  exact RawDCT.RealPChiRouteBridge.rowParityNat_eq_indexParity_val a b r

/-- The natural connector parity used by the executable kernel is the value
of the raw connector parity field. -/
private theorem connectorParityNat_eq_rawParity_val (a b c : ZMod 8) :
    RawDCT.RealPChiKernel.connectorParityNat a b c =
      (rawReal.T.parity a b c).val := by
  rfl

/-- The shifted binary row parity is the raw stored parity plus the
computable regrading cochain. -/
@[simp] private theorem shiftedRowParity_eq (a b : ZMod 8)
    (r : shiftedReal.C.Index a b) :
    shiftedReal.C.rowParity a b r =
      rawRowParityOfShifted a b r +
        shiftNu realComputableNuBeta.data a b := by
  rfl

/-- Reinterpret an underlying coefficient coordinate as the public basis
index used by the saved executable kernel. -/
private def kernelIndex (a : ZMod 8) (basis : Fin (realRepDim a.val)) :
    Fin (RawDCT.RealPChiKernel.coefficientRank a) :=
  cast (congrArg Fin (show
    realRepDim a.val = RawDCT.RealPChiKernel.coefficientRank a from rfl)) basis

/-- Reindex a saved finite row sum directly by the unchanged shifted fusion
table.  This is the row-index specialization of the existing `sumRange`
bridge, not a route evaluation. -/
private theorem sumRange_eq_sumShiftedIndex (a b : ZMod 8)
    (f : ℕ → ℤ) :
    RawDCT.RealPChiKernel.sumRange
        (RawDCT.RealPChiKernel.fusionRank a b) f =
      ∑ r : shiftedReal.C.Index a b, f r.val := by
  change RawDCT.RealPChiKernel.sumRange
      (RawDCT.RealPChiKernel.fusionRank a b) f =
    ∑ r : Fin (RawDCT.RealPChiKernel.fusionRank a b), f r.val
  exact RawDCT.RealPChiKernel.sumRange_eq_sumFin _ _

/-- Reindex a saved coefficient-basis sum by the underlying native basis.
The public and native ranks are definitionally the same stored dimension. -/
private theorem sumRange_eq_sumNativeBasis (a : ZMod 8)
    (f : ℕ → ℤ) :
    RawDCT.RealPChiKernel.sumRange
        (RawDCT.RealPChiKernel.coefficientRank a) f =
      ∑ r : Fin (realRepDim a.val), f r.val := by
  change RawDCT.RealPChiKernel.sumRange
      (RawDCT.RealPChiKernel.coefficientRank a) f =
    ∑ r : Fin (RawDCT.RealPChiKernel.coefficientRank a), f r.val
  exact RawDCT.RealPChiKernel.sumRange_eq_sumFin _ _

/-- Public-index form of the saved pointwise shifted connector bridge.  The
explicit raw-index casts prevent later rewriting from relying on reducibility
of the concrete shifted fusion table. -/
private theorem realShiftedHomCoefficient_apply_public
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c))
    (targetBasis : Fin (realRepDim (a + b + c).val)) :
    Associator.homCoefficient shiftedReal a b c
        sourceAB sourceABC targetBC targetABC targetBasis =
      (rightRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c (rawIndexOfShifted b c targetBC) *
          (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
          leftRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c (rawIndexOfShifted a b sourceAB)) *
        ((RawDCT.RealPChiKernel.connectorLinearCoeff a b c
          targetBC.val targetABC.val sourceAB.val sourceABC.val
          targetBasis.val
          (RawDCT.RealPChiKernel.coefficientUnitIndex
            (a + b + c)).val : ℤ) : ℝ) := by
  change Fin (RawDCT.RealPChiKernel.coefficientRank
    (a + b + c)) at targetBasis
  exact
    realShiftedHomCoefficient_apply a b c sourceAB sourceABC
      targetBC targetABC targetBasis

/-- Public-index form of the multiplication-by-basis connector bridge. -/
private theorem realShiftedHomCoefficient_mul_basis_public
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c))
    (sourceBasis : Fin
      (RawDCT.RealPChiKernel.coefficientRank (a + b + c)))
    (targetBasis : Fin (realRepDim (a + b + c).val)) :
    (shiftedReal.D.algebra (a + b + c)).mul
        (Associator.homCoefficient shiftedReal a b c
          sourceAB sourceABC targetBC targetABC)
        (RawDCT.RealPChiKernel.coefficientBasis
          (a + b + c) sourceBasis) targetBasis =
      (rightRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c (rawIndexOfShifted b c targetBC) *
          (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
          leftRouteFrameSign rawReal.C realComputableNuBeta.data
            a b c (rawIndexOfShifted a b sourceAB)) *
        ((RawDCT.RealPChiKernel.connectorLinearCoeff a b c
          targetBC.val targetABC.val sourceAB.val sourceABC.val
          targetBasis.val sourceBasis.val : ℤ) : ℝ) := by
  change Fin (RawDCT.RealPChiKernel.coefficientRank
    (a + b + c)) at targetBasis
  exact
    realShiftedHomCoefficient_mul_basis a b c sourceAB sourceABC
      targetBC targetABC sourceBasis targetBasis

/-- The four shifted endpoint-row parities of a connector coefficient add
to its raw coefficient-algebra degree.  This is the grade used by both
whiskering twists in `topCoordinateExponent`. -/
private theorem shiftedConnectorRowSum_eq_rawGrade
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c)) :
    shiftedReal.C.rowParity a b sourceAB +
        shiftedReal.C.rowParity (a + b) c sourceABC +
        shiftedReal.C.rowParity b c targetBC +
        shiftedReal.C.rowParity a (b + c) targetABC =
      rawReal.T.parity a b c +
        rawRowParityOfShifted a b sourceAB +
        rawRowParityOfShifted (a + b) c sourceABC +
        rawRowParityOfShifted b c targetBC +
        rawRowParityOfShifted a (b + c) targetABC := by
  rw [shiftedRowParity_eq, shiftedRowParity_eq,
    shiftedRowParity_eq, shiftedRowParity_eq,
    realRawParity_eq_shiftNu_sum]
  ring_nf

/-- The shifted connector coefficient is homogeneous in the raw degree
displayed in the executable kernel, despite the binary regrading. -/
private theorem realShiftedHomCoefficient_memGrade_raw
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c)) :
    (shiftedReal.D.algebra (a + b + c)).MemGrade
      (rawReal.T.parity a b c +
        rawRowParityOfShifted a b sourceAB +
        rawRowParityOfShifted (a + b) c sourceABC +
        rawRowParityOfShifted b c targetBC +
        rawRowParityOfShifted a (b + c) targetABC)
      (Associator.homCoefficient shiftedReal a b c
        sourceAB sourceABC targetBC targetABC) := by
  rw [← shiftedConnectorRowSum_eq_rawGrade a b c
    sourceAB sourceABC targetBC targetABC]
  exact RealAssociatorLaws.realHomCoefficient_memGrade a b c
    sourceAB sourceABC targetBC targetABC

private theorem routeRowTwist_zeroParity_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (x : (dD.algebra a).carrier) :
    RawDCT.routeRowTwist dD a 0 x = x :=
  RawDCT.routeRowTwist_zeroParity (dD.algebra a)
    (hD.algebra_laws a) x

private theorem routeRowTwist_one_at (dD : DData) (hD : DLaws dD)
    (a : ZMod 8) (p : ZMod 2) :
    RawDCT.routeRowTwist dD a p (dD.algebra a).one =
      (dD.algebra a).one :=
  RawDCT.routeRowTwist_one (dD.algebra a) (hD.algebra_laws a) p

/-- Homogeneous inputs turn a row twist into its parity scalar.  The wrapper
fixes the ambient algebra parameter before using the public raw theorem. -/
private theorem routeRowTwist_of_memGrade_at
    (dD : DData) (hD : DLaws dD) (a : ZMod 8)
    (p i : ZMod 2) (x : (dD.algebra a).carrier)
    (hx : (dD.algebra a).MemGrade i x) :
    RawDCT.routeRowTwist dD a p x =
      (dD.algebra a).smul (RawDCT.paritySign (p * i)) x := by
  simpa only [RawDCT.routeRowTwist] using
    RawDCT.routeRowTwist_of_memGrade
      (dD.algebra a) (hD.algebra_laws a) p i x hx

/-- Scalar linearity of a raw binary action coefficient, recovered from
the public tensor-coefficient linearity law. -/
private theorem rawLeftCoeff_smul_left
    (dD : DData) (hD : DLaws dD) (dC : CData dD)
    (hC : CLaws dD hD dC) (a b : ZMod 8)
    (target source : dC.Index a b) (r : ℝ)
    (u : (dD.algebra a).carrier) (v : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source ((dD.algebra a).smul r u) v =
      (dD.algebra (a + b)).smul r
        (dC.leftCoeff a b target source u v) := by
  have h := Tensor.coefficient_smul_left dD hD dC hC a b
    0 0 0 source target r u v
  unfold Tensor.coefficient at h
  rw [routeRowTwist_zeroParity_at dD hD a ((dD.algebra a).smul r u),
    routeRowTwist_zeroParity_at dD hD a u,
    routeRowTwist_zeroParity_at dD hD b v] at h
  simpa only [zero_add, zero_mul, RawDCT.shiftParitySign_zero,
    (hD.algebra_laws (a + b)).one_smul] using h

private theorem rawLeftCoeff_smul_right
    (dD : DData) (hD : DLaws dD) (dC : CData dD)
    (hC : CLaws dD hD dC) (a b : ZMod 8)
    (target source : dC.Index a b) (r : ℝ)
    (u : (dD.algebra a).carrier) (v : (dD.algebra b).carrier) :
    dC.leftCoeff a b target source u ((dD.algebra b).smul r v) =
      (dD.algebra (a + b)).smul r
        (dC.leftCoeff a b target source u v) := by
  have h := Tensor.coefficient_smul_right dD hD dC hC a b
    0 0 0 source target r u v
  unfold Tensor.coefficient at h
  rw [routeRowTwist_zeroParity_at dD hD a u,
    routeRowTwist_zeroParity_at dD hD b ((dD.algebra b).smul r v),
    routeRowTwist_zeroParity_at dD hD b v] at h
  simpa only [zero_add, zero_mul, RawDCT.shiftParitySign_zero,
    (hD.algebra_laws (a + b)).one_smul] using h

/-- Tensoring a homogeneous coefficient on the right with an unchanged
atomic identity produces the raw left-slot fusion coefficient and the one
combined whisker/regrading sign. -/
private theorem tensorCoefficient_hom_one
    (a b : ZMod 8) (s t i : ZMod 2)
    (source target : shiftedReal.C.Index a b)
    (x : (shiftedReal.D.algebra a).carrier)
    (hx : (shiftedReal.D.algebra a).MemGrade i x) :
    Tensor.coefficient shiftedReal.D shiftedReal.C a b s t t
        source target x (shiftedReal.D.algebra b).one =
      (shiftedReal.D.algebra (a + b)).smul
        (RawDCT.paritySign
          ((t + shiftNu realComputableNuBeta.data a b) * i))
        (rawReal.C.leftCoeff a b target source x
          (rawReal.D.algebra b).one) := by
  let sourceRaw : rawReal.C.Index a b := source
  let targetRaw : rawReal.C.Index a b := target
  let xRaw : (rawReal.D.algebra a).carrier := x
  have hxRaw : (rawReal.D.algebra a).MemGrade i xRaw := hx
  have htwist : (rawReal.D.algebra a).MemGrade i
      (RawDCT.routeRowTwist rawReal.D a t xRaw) :=
    RawDCT.routeRowTwist_memGrade (rawReal.D.algebra a)
      (realRawDCT.laws.D.algebra_laws a) t i xRaw hxRaw
  unfold Tensor.coefficient
  rw [ZModModule.add_self, mul_zero, shiftParitySign_zero,
    routeRowTwist_one_at shiftedReal.D
      realComputableShiftedRawDCT.laws.D,
    (realComputableShiftedRawDCT.laws.D.algebra_laws (a + b)).one_smul]
  change rawReal.C.leftCoeff a b targetRaw sourceRaw
      (RawDCT.routeRowTwist rawReal.D a
        (shiftNu realComputableNuBeta.data a b)
        (RawDCT.routeRowTwist rawReal.D a t xRaw))
      (RawDCT.routeRowTwist rawReal.D b
        (shiftNu realComputableNuBeta.data a b)
        (rawReal.D.algebra b).one) = _
  rw [routeRowTwist_of_memGrade_at rawReal.D realRawDCT.laws.D a
      (shiftNu realComputableNuBeta.data a b) i _ htwist,
    routeRowTwist_one_at rawReal.D realRawDCT.laws.D,
    rawLeftCoeff_smul_left rawReal.D realRawDCT.laws.D
      rawReal.C realRawDCT.laws.C,
    routeRowTwist_of_memGrade_at rawReal.D realRawDCT.laws.D a
      t i xRaw hxRaw,
    rawLeftCoeff_smul_left rawReal.D realRawDCT.laws.D
      rawReal.C realRawDCT.laws.C,
    ← (realRawDCT.laws.D.algebra_laws (a + b)).smul_assoc,
    ← shiftParitySign_add]
  congr 1
  ring

/-- Tensoring an unchanged identity on the left with a homogeneous right
coefficient records the outer tensor sign, the right-row twist, and the
binary regrading sign in one exponent. -/
private theorem tensorCoefficient_one_hom
    (a b : ZMod 8) (s t t' i : ZMod 2)
    (source target : shiftedReal.C.Index a b)
    (x : (shiftedReal.D.algebra b).carrier)
    (hx : (shiftedReal.D.algebra b).MemGrade i x) :
    Tensor.coefficient shiftedReal.D shiftedReal.C a b s t t'
        source target (shiftedReal.D.algebra a).one x =
      (shiftedReal.D.algebra (a + b)).smul
        (RawDCT.paritySign
          (s * (t + t') +
            (s + shiftNu realComputableNuBeta.data a b) * i))
        (rawReal.C.leftCoeff a b target source
          (rawReal.D.algebra a).one x) := by
  let sourceRaw : rawReal.C.Index a b := source
  let targetRaw : rawReal.C.Index a b := target
  let xRaw : (rawReal.D.algebra b).carrier := x
  have hxRaw : (rawReal.D.algebra b).MemGrade i xRaw := hx
  have htwist : (rawReal.D.algebra b).MemGrade i
      (RawDCT.routeRowTwist rawReal.D b s xRaw) :=
    RawDCT.routeRowTwist_memGrade (rawReal.D.algebra b)
      (realRawDCT.laws.D.algebra_laws b) s i xRaw hxRaw
  unfold Tensor.coefficient
  rw [routeRowTwist_one_at shiftedReal.D
    realComputableShiftedRawDCT.laws.D]
  change (rawReal.D.algebra (a + b)).smul
      (RawDCT.paritySign (s * (t + t')))
      (rawReal.C.leftCoeff a b targetRaw sourceRaw
        (RawDCT.routeRowTwist rawReal.D a
          (shiftNu realComputableNuBeta.data a b)
          (rawReal.D.algebra a).one)
        (RawDCT.routeRowTwist rawReal.D b
          (shiftNu realComputableNuBeta.data a b)
          (RawDCT.routeRowTwist rawReal.D b s xRaw))) = _
  rw [routeRowTwist_one_at rawReal.D realRawDCT.laws.D,
    routeRowTwist_of_memGrade_at rawReal.D realRawDCT.laws.D b
      (shiftNu realComputableNuBeta.data a b) i _ htwist,
    rawLeftCoeff_smul_right rawReal.D realRawDCT.laws.D
      rawReal.C realRawDCT.laws.C,
    routeRowTwist_of_memGrade_at rawReal.D realRawDCT.laws.D b
      s i xRaw hxRaw,
    rawLeftCoeff_smul_right rawReal.D realRawDCT.laws.D
      rawReal.C realRawDCT.laws.C,
    ← (realRawDCT.laws.D.algebra_laws (a + b)).smul_assoc,
    ← (realRawDCT.laws.D.algebra_laws (a + b)).smul_assoc,
    ← shiftParitySign_add, ← shiftParitySign_add]
  congr 1
  ring

/-- For an even categorical right morphism, its two endpoint shifts add to
the coefficient-algebra grade, so the outer tensor sign cancels the ordinary
right-row twist.  Only the binary `nu` twist remains. -/
private theorem tensorCoefficient_one_hom_of_endpoint_sum
    (a b : ZMod 8) (s t t' i : ZMod 2)
    (source target : shiftedReal.C.Index a b)
    (x : (shiftedReal.D.algebra b).carrier)
    (hx : (shiftedReal.D.algebra b).MemGrade i x)
    (hEndpoint : t + t' = i) :
    Tensor.coefficient shiftedReal.D shiftedReal.C a b s t t'
        source target (shiftedReal.D.algebra a).one x =
      (shiftedReal.D.algebra (a + b)).smul
        (RawDCT.paritySign
          (shiftNu realComputableNuBeta.data a b * i))
        (rawReal.C.leftCoeff a b target source
          (rawReal.D.algebra a).one x) := by
  rw [tensorCoefficient_one_hom a b s t t' i source target x hx]
  congr 1
  rw [hEndpoint]
  ring_nf
  rw [show (2 : ZMod 2) = 0 by decide]
  ring

/-- The common-sign form used when the shifted scalar-coordinate theorem is
inserted between the actual top and bottom matrix coefficients. -/
private theorem realCoordinateCommonExponent_eq
    (a b c d : ZMod 8)
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD : ZMod 2) :
    topCoordinateExponent
        sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
        (shiftNu realComputableNuBeta.data a b)
        (shiftNu realComputableNuBeta.data b c)
        (shiftNu realComputableNuBeta.data c d)
        (shiftNu realComputableNuBeta.data (a + b) c)
        (shiftNu realComputableNuBeta.data a (b + c))
        (shiftNu realComputableNuBeta.data (a + b + c) d)
        (shiftNu realComputableNuBeta.data (b + c) d)
        (shiftNu realComputableNuBeta.data b (c + d))
        (shiftNu realComputableNuBeta.data (a + b) (c + d))
        (shiftNu realComputableNuBeta.data a (b + c + d))
        (rawReal.T.parity a b c) (rawReal.T.parity b c d) +
      (shiftPentagonTopDegree rawReal realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) +
        rawReal.T.parity a (b + c) d * pBC) =
    bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
        (shiftNu realComputableNuBeta.data a b)
        (shiftNu realComputableNuBeta.data c d)
        (shiftNu realComputableNuBeta.data (a + b) c)
        (shiftNu realComputableNuBeta.data (a + b + c) d)
        (shiftNu realComputableNuBeta.data (a + b) (c + d))
        (shiftNu realComputableNuBeta.data a (b + c + d)) +
      (shiftPentagonBottomDegree realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) +
        rawReal.T.parity (a + b) c d * pAB +
        pCD * (rawReal.T.parity a b (c + d) + pAB)) := by
  simpa only [shiftPentagonTopDegree, shiftPentagonBottomDegree,
    rawParity, shiftNu, ofAdd_mul_eq, toAdd_ofAdd,
    _root_.add_assoc] using
    coordinateCommonExponent_eq
      sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
      (shiftNu realComputableNuBeta.data a b)
      (shiftNu realComputableNuBeta.data b c)
      (shiftNu realComputableNuBeta.data c d)
      (shiftNu realComputableNuBeta.data (a + b) c)
      (shiftNu realComputableNuBeta.data a (b + c))
      (shiftNu realComputableNuBeta.data (a + b + c) d)
      (shiftNu realComputableNuBeta.data (b + c) d)
      (shiftNu realComputableNuBeta.data b (c + d))
      (shiftNu realComputableNuBeta.data (a + b) (c + d))
      (shiftNu realComputableNuBeta.data a (b + c + d))
      (rawReal.T.parity a b c)
      (rawReal.T.parity a (b + c) d)
      (rawReal.T.parity b c d)
      (rawReal.T.parity (a + b) c d)
      (rawReal.T.parity a b (c + d))
      (by simpa only [_root_.add_assoc] using
        realRawParity_eq_shiftNu_sum a b c)
      (by simpa only [_root_.add_assoc] using
        realRawParity_eq_shiftNu_sum a (b + c) d)
      (by simpa only [_root_.add_assoc] using
        realRawParity_eq_shiftNu_sum b c d)
      (by simpa only [_root_.add_assoc] using
        realRawParity_eq_shiftNu_sum (a + b) c d)
      (by simpa only [_root_.add_assoc] using
        realRawParity_eq_shiftNu_sum a b (c + d))

/-- Real-valued form of the common endpoint sign.  Its three kernel factors
are exactly the casts supplied by `cast_koszulSign_eq_paritySign`. -/
private theorem realCoordinateCommonSign_eq
    (a b c d : ZMod 8)
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD : ZMod 2) :
    RawDCT.paritySign
        (topCoordinateExponent
          sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
          (shiftNu realComputableNuBeta.data a b)
          (shiftNu realComputableNuBeta.data b c)
          (shiftNu realComputableNuBeta.data c d)
          (shiftNu realComputableNuBeta.data (a + b) c)
          (shiftNu realComputableNuBeta.data a (b + c))
          (shiftNu realComputableNuBeta.data (a + b + c) d)
          (shiftNu realComputableNuBeta.data (b + c) d)
          (shiftNu realComputableNuBeta.data b (c + d))
          (shiftNu realComputableNuBeta.data (a + b) (c + d))
          (shiftNu realComputableNuBeta.data a (b + c + d))
          (rawReal.T.parity a b c) (rawReal.T.parity b c d)) *
      (RawDCT.paritySign
          (shiftPentagonTopDegree rawReal realComputableNuBeta.data
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
            (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
        RawDCT.paritySign (rawReal.T.parity a (b + c) d * pBC)) =
    RawDCT.paritySign
        (bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
          (shiftNu realComputableNuBeta.data a b)
          (shiftNu realComputableNuBeta.data c d)
          (shiftNu realComputableNuBeta.data (a + b) c)
          (shiftNu realComputableNuBeta.data (a + b + c) d)
          (shiftNu realComputableNuBeta.data (a + b) (c + d))
          (shiftNu realComputableNuBeta.data a (b + c + d))) *
      (RawDCT.paritySign
          (shiftPentagonBottomDegree realComputableNuBeta.data
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
            (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
        (RawDCT.paritySign (rawReal.T.parity (a + b) c d * pAB) *
          RawDCT.paritySign
            (pCD * (rawReal.T.parity a b (c + d) + pAB)))) := by
  simpa only [shiftParitySign_add, mul_assoc] using congrArg RawDCT.paritySign
    (realCoordinateCommonExponent_eq a b c d sY sZ
      pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD)

set_option maxHeartbeats 1600000 in
/-- Complete scalar reconciliation of one top-route summand with the
corresponding bottom-route summand.  All row parities and saved kernel
values are abstract; the shift data, frame degrees, and connector parities
are concrete.  The proof merges the eleven top signs, inserts two squared
signs, and applies the already proved common-sign comparison. -/
private theorem topSummand_eq_bottomSummand (a b c d : ZMod 8)
    (sY sZ pAB pABC pBC pA_BC pBC_D pCD pBCD : ZMod 2)
    (K1 K2 K3 K4 K5 : ℝ) :
    RawDCT.paritySign
        ((sZ + shiftNu realComputableNuBeta.data (a + b + c) d) *
          (rawReal.T.parity a b c + pAB + pABC + pBC + pA_BC)) *
      (RawDCT.paritySign
          ((pAB + shiftNu realComputableNuBeta.data a b) * sY) *
        (RawDCT.paritySign
            (shiftNu realComputableNuBeta.data a (b + c) * pBC) *
          (↑(shiftBeta realComputableNuBeta.data a b c))⁻¹ *
          RawDCT.paritySign
            (shiftNu realComputableNuBeta.data (a + b) c * pAB) *
          K1 * K2)) *
      (RawDCT.paritySign
          ((pA_BC + shiftNu realComputableNuBeta.data a (b + c)) * sZ) *
        (RawDCT.paritySign
            (shiftNu realComputableNuBeta.data a (b + c + d) * pBC_D) *
          (↑(shiftBeta realComputableNuBeta.data a (b + c) d))⁻¹ *
          RawDCT.paritySign
            (shiftNu realComputableNuBeta.data (a + b + c) d * pA_BC) *
          K3)) *
      (RawDCT.paritySign
          (shiftNu realComputableNuBeta.data a (b + c + d) *
            (rawReal.T.parity b c d + pBC + pBC_D + pCD + pBCD)) *
        (RawDCT.paritySign
            ((pBC + shiftNu realComputableNuBeta.data b c) * sZ) *
          (RawDCT.paritySign
              (shiftNu realComputableNuBeta.data b (c + d) * pCD) *
            (↑(shiftBeta realComputableNuBeta.data b c d))⁻¹ *
            RawDCT.paritySign
              (shiftNu realComputableNuBeta.data (b + c) d * pBC) *
            K4 * K5))) =
    RawDCT.paritySign
        (bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
          (shiftNu realComputableNuBeta.data a b)
          (shiftNu realComputableNuBeta.data c d)
          (shiftNu realComputableNuBeta.data (a + b) c)
          (shiftNu realComputableNuBeta.data (a + b + c) d)
          (shiftNu realComputableNuBeta.data (a + b) (c + d))
          (shiftNu realComputableNuBeta.data a (b + c + d))) *
      (RawDCT.paritySign
          (shiftPentagonBottomDegree realComputableNuBeta.data
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
            (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
        (RawDCT.paritySign (rawReal.T.parity (a + b) c d * pAB) *
          RawDCT.paritySign (pCD * (rawReal.T.parity a b (c + d) + pAB)))) *
      ((↑(shiftBeta realComputableNuBeta.data a b c))⁻¹ *
        (↑(shiftBeta realComputableNuBeta.data a (b + c) d))⁻¹ *
        (↑(shiftBeta realComputableNuBeta.data b c d))⁻¹ *
        RawDCT.paritySign
          (shiftPentagonTopDegree rawReal realComputableNuBeta.data
            (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
            (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
        (K1 * K2 *
          RawDCT.paritySign (rawReal.T.parity a (b + c) d * pBC) *
          K3 * K4 * K5)) := by
  have hmerge := topCoordinateParityProduct_eq
    sY sZ pAB pABC pBC pA_BC pBC_D 0 pCD pBCD
    (shiftNu realComputableNuBeta.data a b)
    (shiftNu realComputableNuBeta.data b c)
    (shiftNu realComputableNuBeta.data c d)
    (shiftNu realComputableNuBeta.data (a + b) c)
    (shiftNu realComputableNuBeta.data a (b + c))
    (shiftNu realComputableNuBeta.data (a + b + c) d)
    (shiftNu realComputableNuBeta.data (b + c) d)
    (shiftNu realComputableNuBeta.data b (c + d))
    (shiftNu realComputableNuBeta.data (a + b) (c + d))
    (shiftNu realComputableNuBeta.data a (b + c + d))
    (rawReal.T.parity a b c) (rawReal.T.parity b c d)
  have hsign := realCoordinateCommonSign_eq a b c d
    sY sZ pAB pABC pBC pA_BC pBC_D 0 pCD pBCD
  have hsqTop : RawDCT.paritySign
      (shiftPentagonTopDegree rawReal realComputableNuBeta.data
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
      RawDCT.paritySign
        (shiftPentagonTopDegree rawReal realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) = 1 := by
    rw [← pow_two]
    exact paritySign_sq _
  have hsqMid : RawDCT.paritySign (rawReal.T.parity a (b + c) d * pBC) *
      RawDCT.paritySign (rawReal.T.parity a (b + c) d * pBC) = 1 := by
    rw [← pow_two]
    exact paritySign_sq _
  calc
    _ = (RawDCT.paritySign
          ((pAB + shiftNu realComputableNuBeta.data a b) * sY) *
        RawDCT.paritySign
          ((pA_BC + shiftNu realComputableNuBeta.data a (b + c)) * sZ) *
        RawDCT.paritySign
          ((pBC + shiftNu realComputableNuBeta.data b c) * sZ) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data a (b + c) * pBC) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data (a + b) c * pAB) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data a (b + c + d) * pBC_D) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data (a + b + c) d * pA_BC) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data b (c + d) * pCD) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data (b + c) d * pBC) *
        RawDCT.paritySign
          ((sZ + shiftNu realComputableNuBeta.data (a + b + c) d) *
            (rawReal.T.parity a b c + pAB + pABC + pBC + pA_BC)) *
        RawDCT.paritySign
          (shiftNu realComputableNuBeta.data a (b + c + d) *
            (rawReal.T.parity b c d + pBC + pBC_D + pCD + pBCD))) *
        ((↑(shiftBeta realComputableNuBeta.data a b c))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data a (b + c) d))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data b c d))⁻¹ *
          (K1 * K2 * K3 * K4 * K5)) := by
      ring
    _ = RawDCT.paritySign
          (topCoordinateExponent
            sY sZ pAB pABC pBC pA_BC pBC_D 0 pCD pBCD
            (shiftNu realComputableNuBeta.data a b)
            (shiftNu realComputableNuBeta.data b c)
            (shiftNu realComputableNuBeta.data c d)
            (shiftNu realComputableNuBeta.data (a + b) c)
            (shiftNu realComputableNuBeta.data a (b + c))
            (shiftNu realComputableNuBeta.data (a + b + c) d)
            (shiftNu realComputableNuBeta.data (b + c) d)
            (shiftNu realComputableNuBeta.data b (c + d))
            (shiftNu realComputableNuBeta.data (a + b) (c + d))
            (shiftNu realComputableNuBeta.data a (b + c + d))
            (rawReal.T.parity a b c) (rawReal.T.parity b c d)) *
        ((↑(shiftBeta realComputableNuBeta.data a b c))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data a (b + c) d))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data b c d))⁻¹ *
          (K1 * K2 * K3 * K4 * K5)) := by
      rw [hmerge]
    _ = (RawDCT.paritySign
          (topCoordinateExponent
            sY sZ pAB pABC pBC pA_BC pBC_D 0 pCD pBCD
            (shiftNu realComputableNuBeta.data a b)
            (shiftNu realComputableNuBeta.data b c)
            (shiftNu realComputableNuBeta.data c d)
            (shiftNu realComputableNuBeta.data (a + b) c)
            (shiftNu realComputableNuBeta.data a (b + c))
            (shiftNu realComputableNuBeta.data (a + b + c) d)
            (shiftNu realComputableNuBeta.data (b + c) d)
            (shiftNu realComputableNuBeta.data b (c + d))
            (shiftNu realComputableNuBeta.data (a + b) (c + d))
            (shiftNu realComputableNuBeta.data a (b + c + d))
            (rawReal.T.parity a b c) (rawReal.T.parity b c d)) *
          (RawDCT.paritySign
              (shiftPentagonTopDegree rawReal realComputableNuBeta.data
                (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
                (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
            RawDCT.paritySign
              (rawReal.T.parity a (b + c) d * pBC))) *
        (RawDCT.paritySign
            (shiftPentagonTopDegree rawReal realComputableNuBeta.data
              (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
              (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
          RawDCT.paritySign
            (rawReal.T.parity a (b + c) d * pBC)) *
        ((↑(shiftBeta realComputableNuBeta.data a b c))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data a (b + c) d))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data b c d))⁻¹ *
          (K1 * K2 * K3 * K4 * K5)) := by
      rw [show ∀ x y u v : ℝ, x * (y * u) * (y * u) * v =
          x * (y * y) * (u * u) * v from by intros; ring]
      rw [hsqTop, hsqMid, mul_one, mul_one]
    _ = (RawDCT.paritySign
          (bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
            (shiftNu realComputableNuBeta.data a b)
            (shiftNu realComputableNuBeta.data c d)
            (shiftNu realComputableNuBeta.data (a + b) c)
            (shiftNu realComputableNuBeta.data (a + b + c) d)
            (shiftNu realComputableNuBeta.data (a + b) (c + d))
            (shiftNu realComputableNuBeta.data a (b + c + d))) *
          (RawDCT.paritySign
              (shiftPentagonBottomDegree realComputableNuBeta.data
                (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
                (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
            (RawDCT.paritySign (rawReal.T.parity (a + b) c d * pAB) *
              RawDCT.paritySign
                (pCD * (rawReal.T.parity a b (c + d) + pAB))))) *
        (RawDCT.paritySign
            (shiftPentagonTopDegree rawReal realComputableNuBeta.data
              (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
              (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
          RawDCT.paritySign
            (rawReal.T.parity a (b + c) d * pBC)) *
        ((↑(shiftBeta realComputableNuBeta.data a b c))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data a (b + c) d))⁻¹ *
          (↑(shiftBeta realComputableNuBeta.data b c d))⁻¹ *
          (K1 * K2 * K3 * K4 * K5)) := by
      rw [hsign]
    _ = _ := by ring

/-- Coercing the existing top shift scalar exposes precisely its three
stored `beta⁻¹` factors and the top shift parity from the ledger. -/
private theorem coe_shiftPentagonTopScalar (a b c d : ZMod 8) :
    (shiftPentagonTopScalar rawReal realComputableNuBeta.data
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝ) =
      (↑(shiftBeta realComputableNuBeta.data a b c)⁻¹ : ℝ) *
      (↑(shiftBeta realComputableNuBeta.data a (b + c) d)⁻¹ : ℝ) *
      (↑(shiftBeta realComputableNuBeta.data b c d)⁻¹ : ℝ) *
      RawDCT.paritySign
        (shiftPentagonTopDegree rawReal realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) := by
  unfold shiftPentagonTopScalar shiftBeta
  simp only [Units.val_mul, Units.val_inv_eq_inv_val,
    coe_sgn_eq_paritySign, ofAdd_mul_eq]

/-- Coercing the existing bottom shift scalar exposes its two stored
`beta⁻¹` factors and the bottom shift parity from the ledger. -/
private theorem coe_shiftPentagonBottomScalar (a b c d : ZMod 8) :
    (shiftPentagonBottomScalar realComputableNuBeta.data
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
        (Multiplicative.ofAdd c) (Multiplicative.ofAdd d) : ℝ) =
      (↑(shiftBeta realComputableNuBeta.data (a + b) c d)⁻¹ : ℝ) *
      (↑(shiftBeta realComputableNuBeta.data a b (c + d))⁻¹ : ℝ) *
      RawDCT.paritySign
        (shiftPentagonBottomDegree realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) := by
  unfold shiftPentagonBottomScalar shiftBeta
  simp only [Units.val_mul, Units.val_inv_eq_inv_val,
    coe_sgn_eq_paritySign, ofAdd_mul_eq]

/-! ## The two finite matrix routes -/

private def topRoute (W X Y Z : Obj) :
    Hom shiftedReal.D (tensorObj (tensorObj (tensorObj W X) Y) Z)
      (tensorObj W (tensorObj X (tensorObj Y Z))) :=
  Hom.comp
    (Hom.comp
      (Tensor.hom shiftedReal.D shiftedReal.C
        (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z))
      (RealAssociator.hom W (tensorObj X Y) Z))
    (Tensor.hom shiftedReal.D shiftedReal.C (Hom.id shiftedReal.D W)
      (RealAssociator.hom X Y Z))

private def bottomRoute (W X Y Z : Obj) :
    Hom shiftedReal.D (tensorObj (tensorObj (tensorObj W X) Y) Z)
      (tensorObj W (tensorObj X (tensorObj Y Z))) :=
  Hom.comp
    (RealAssociator.hom (tensorObj W X) Y Z)
    (RealAssociator.hom W X (tensorObj Y Z))

/-! ### Coefficient sums for the bottom route -/

@[implicit_reducible]
private def concreteAlgebraAddCommGroup (a : ZMod 8) :
    AddCommGroup (shiftedReal.D.algebra a).carrier := by
  let d := shiftedReal.D.algebra a
  let h := realComputableShiftedRawDCT.laws.D.algebra_laws a
  letI : Zero d.carrier := ⟨d.zero⟩
  letI : Add d.carrier := ⟨d.add⟩
  letI : Neg d.carrier := ⟨d.neg⟩
  letI : Sub d.carrier := ⟨fun x y => d.add x (d.neg y)⟩
  exact
    { add_assoc := h.add_assoc
      zero_add := h.zero_add
      add_zero := h.add_zero
      neg_add_cancel := h.neg_add
      add_comm := h.add_comm
      sub_eq_add_neg := fun _ _ => rfl
      nsmul := nsmulRec
      zsmul := zsmulRec }

private local instance (priority := 10000) (a : ZMod 8) :
    AddCommGroup (shiftedReal.D.algebra a).carrier :=
  concreteAlgebraAddCommGroup a

/-- Reading a coefficient commutes with the fixed atomic finite sum.  This
is the atomic counterpart of `realComp_coeff_as_sum`, used below to expose
the second middle index of the three-edge route. -/
private theorem atomHom_finSum_coeff {X Y : Atom} {n : ℕ}
    (f : Fin n → AtomHom shiftedReal.D X Y) (hXY : X.label = Y.label) :
    (AtomHom.finSum n f).coeff hXY = ∑ i, (f i).coeff hXY := by
  induction n with
  | zero =>
      simp only [AtomHom.finSum, AtomHom.coeff_zero]
      rfl
  | succ n ih =>
      simp only [AtomHom.finSum, AtomHom.coeff_add]
      rw [ih, Fin.sum_univ_castSucc]
      rfl

private theorem cast_cast_eq {A B C : Type} (hAB : A = B) (hBC : B = C)
    (u : A) : cast hBC (cast hAB u) = cast (hAB.trans hBC) u := by
  subst B
  subst C
  rfl

private theorem cast_proof_irrel {A B : Sort _} (h h' : A = B) (u : A) :
    cast h u = cast h' u := by
  rw [Subsingleton.elim h h']

/-- The coefficient carrier of the shifted real algebra is the public finite
coordinate type.  Keeping this equality opaque lets tactic elaboration see an
explicit function type without unfolding the whole shifted raw DCT. -/
private theorem shiftedCarrier_eq_coeff (a : ZMod 8) :
    (shiftedReal.D.algebra a).carrier = RModCoordinate.Coeff a := rfl

/-- Observe an abstract shifted-algebra element as its concrete coordinate
function.  This is a definitional transport, not a numerical evaluation. -/
private def observeCoefficient (a : ZMod 8)
    (x : (shiftedReal.D.algebra a).carrier) : RModCoordinate.Coeff a :=
  cast (shiftedCarrier_eq_coeff a) x

/-- Reinterpret the public kernel's basis index as the underlying coordinate
index.  The two bounds are definitionally equal, but naming this transport
keeps applications type-correct at Lean's `instances` transparency level. -/
private def coefficientIndex (a : ZMod 8)
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank a)) :
    Fin (realRepDim a.val) :=
  cast (congrArg Fin (show
    RawDCT.RealPChiKernel.coefficientRank a = realRepDim a.val from rfl)) basis

private theorem coefficientIndex_kernelIndex (a : ZMod 8)
    (basis : Fin (realRepDim a.val)) :
    coefficientIndex a (kernelIndex a basis) = basis := by
  rfl

@[simp] private theorem coefficientIndex_val (a : ZMod 8)
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank a)) :
    (coefficientIndex a basis).val = basis.val := by
  rfl

@[simp] private theorem kernelIndex_val (a : ZMod 8)
    (basis : Fin (realRepDim a.val)) :
    (kernelIndex a basis).val = basis.val := by
  rfl

/-- Reindexing a finite type along an equality preserves the stored natural
number.  This is the value-level form needed after a transported coefficient
has already been observed. -/
@[simp] private theorem finCongr_symm_val {m n : ℕ} (h : m = n)
    (i : Fin n) : ((finCongr h).symm i).val = i.val := by
  subst n
  rfl

private theorem cast_injective {A B : Sort _} (h : A = B) :
    Function.Injective (cast h) := by
  intro x y hxy
  cases h
  exact hxy

private theorem observeCoefficient_injective (a : ZMod 8) :
    Function.Injective (observeCoefficient a) :=
  cast_injective (shiftedCarrier_eq_coeff a)

private theorem observeCoefficient_sum (a : ZMod 8)
    {I : Type} [Fintype I]
    (f : I → (shiftedReal.D.algebra a).carrier) :
    observeCoefficient a (∑ i, f i) =
      ∑ i, observeCoefficient a (f i) := by
  rfl

private theorem observeCoefficient_mul (a : ZMod 8)
    (x y : (shiftedReal.D.algebra a).carrier) :
    observeCoefficient a ((shiftedReal.D.algebra a).mul x y) =
      RModCoordinate.Coeff.mul a
        (observeCoefficient a x) (observeCoefficient a y) := by
  rfl

private theorem observeCoefficient_smul (a : ZMod 8) (r : ℝ)
    (x : (shiftedReal.D.algebra a).carrier) :
    observeCoefficient a ((shiftedReal.D.algebra a).smul r x) =
      RModCoordinate.Coeff.smul a r (observeCoefficient a x) := by
  rfl

/-- Evaluation of an equality-transported concrete coefficient only
reindexes its finite coordinate.  In particular, no coefficient table is
evaluated by this transport. -/
private theorem cast_algebra_coeff_apply {a b : ZMod 8} (h : a = b)
    (x : (shiftedReal.D.algebra a).carrier)
    (basis : Fin (realRepDim b.val)) :
    (cast (congrArg
      (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) h) x) basis =
      x ((finCongr (congrArg
        (fun t : ZMod 8 => realRepDim t.val) h)).symm basis) := by
  subst b
  rfl

/-- Multiplication by a transported coefficient on a canonical basis vector
is the same multiplication before transport, with source and target basis
indices reindexed along the label equality. -/
private theorem cast_algebra_mul_basis_apply {a b : ZMod 8} (h : a = b)
    (x : (shiftedReal.D.algebra a).carrier)
    (sourceBasis targetBasis : Fin (realRepDim b.val)) :
    RModCoordinate.Coeff.mul b
        (cast (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) h) x)
        (RawDCT.RealPChiKernel.coefficientBasis b sourceBasis) targetBasis =
      RModCoordinate.Coeff.mul a x
        (RawDCT.RealPChiKernel.coefficientBasis a
          ((finCongr (congrArg
            (fun t : ZMod 8 => realRepDim t.val) h)).symm sourceBasis))
        ((finCongr (congrArg
          (fun t : ZMod 8 => realRepDim t.val) h)).symm targetBasis) := by
  subst b
  rfl

/-- Coordinate observation commutes with label transport and evaluation. -/
private theorem observed_cast_algebra_coeff_apply {a b : ZMod 8}
    (h : a = b) (x : (shiftedReal.D.algebra a).carrier)
    (basis : Fin (realRepDim b.val)) :
    observeCoefficient b
        (cast (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) h) x) basis =
      observeCoefficient a x
        ((finCongr (congrArg
          (fun t : ZMod 8 => realRepDim t.val) h)).symm basis) := by
  subst b
  rfl

/-- The observed transported coefficient can be used as the left input of
coordinate multiplication without exposing the abstract carrier. -/
private theorem observed_cast_algebra_mul_basis_apply {a b : ZMod 8}
    (h : a = b) (x : (shiftedReal.D.algebra a).carrier)
    (sourceBasis : Fin (RawDCT.RealPChiKernel.coefficientRank b))
    (targetBasis : Fin (realRepDim b.val)) :
    RModCoordinate.Coeff.mul b
        (observeCoefficient b
          (cast (congrArg
            (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) h) x))
        (RawDCT.RealPChiKernel.coefficientBasis b sourceBasis) targetBasis =
      RModCoordinate.Coeff.mul a (observeCoefficient a x)
        (RawDCT.RealPChiKernel.coefficientBasis a
          ((finCongr (congrArg
            RawDCT.RealPChiKernel.coefficientRank h)).symm sourceBasis))
        ((finCongr (congrArg
          (fun t : ZMod 8 => realRepDim t.val) h)).symm targetBasis) := by
  subst b
  rfl

/-- An observed shifted connector can be read by the existing pointwise
connector bridge. -/
private theorem observed_realShiftedHomCoefficient_apply_eq
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c))
    (targetBasis : Fin (RawDCT.RealPChiKernel.coefficientRank
      (a + b + c))) :
    observeCoefficient (a + b + c)
        (Associator.homCoefficient shiftedReal a b c
          sourceAB sourceABC targetBC targetABC) targetBasis =
      Associator.homCoefficient shiftedReal a b c
        sourceAB sourceABC targetBC targetABC targetBasis := by
  rfl

/-- The observed connector is also definitionally the input used by the
existing multiplication-by-basis bridge. -/
private theorem observed_realShiftedHomCoefficient_mul_basis_eq
    (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c))
    (sourceBasis targetBasis : Fin
      (RawDCT.RealPChiKernel.coefficientRank (a + b + c))) :
    RModCoordinate.Coeff.mul (a + b + c)
        (observeCoefficient (a + b + c)
          (Associator.homCoefficient shiftedReal a b c
            sourceAB sourceABC targetBC targetABC))
        (RawDCT.RealPChiKernel.coefficientBasis
          (a + b + c) sourceBasis) targetBasis =
      (shiftedReal.D.algebra (a + b + c)).mul
        (Associator.homCoefficient shiftedReal a b c
          sourceAB sourceABC targetBC targetABC)
        (RawDCT.RealPChiKernel.coefficientBasis
          (a + b + c) sourceBasis) targetBasis := by
  rfl

private theorem cast_algebra_mul_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier)
    (u v : (dD.algebra a).carrier) :
    cast h ((dD.algebra a).mul u v) =
      (dD.algebra b).mul (cast h u) (cast h v) := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

/-- Transport along a label equality commutes with a finite sum.  This is a
pure transport fact; it does not inspect any connector or fusion-table entry. -/
private theorem cast_algebra_sum_of_label_eq
    {a b : ZMod 8} (hab : a = b) {I : Type} [Fintype I]
    (f : I → (shiftedReal.D.algebra a).carrier) :
    cast (congrArg
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) hab)
        (∑ i, f i) =
      ∑ i, cast (congrArg
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) hab) (f i) := by
  subst b
  rfl

/-- Evaluation of a finite sum in the concrete coefficient algebra is
pointwise.  Stating the source with the algebra carrier keeps the route
transport lemmas abstract while exposing the stored function coordinates
only at the final observation step. -/
private theorem coefficient_algebra_sum_apply (a : ZMod 8)
    {I : Type} [Fintype I]
    (f : I → (shiftedReal.D.algebra a).carrier)
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank a)) :
    (∑ i, f i) basis = ∑ i, (f i) basis := by
  change (∑ i, (f i : RModCoordinate.Coeff a)) basis = _
  exact Finset.sum_apply basis Finset.univ f

/-- The executable real coefficient algebra stores the public coordinate
multiplication literally.  We expose it together with coordinate evaluation,
so no intermediate term asks Lean to treat an abstract carrier as a function. -/
private theorem shifted_algebra_mul_apply (a : ZMod 8)
    (x y : (shiftedReal.D.algebra a).carrier)
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank a)) :
    ((shiftedReal.D.algebra a).mul x y) basis =
      RModCoordinate.Coeff.mul a x y basis := rfl

/-- Applied threefold multiplication has the same concrete coordinate form. -/
private theorem shifted_algebra_triple_mul_apply (a : ZMod 8)
    (x y z : (shiftedReal.D.algebra a).carrier)
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank a)) :
    ((shiftedReal.D.algebra a).mul x
      ((shiftedReal.D.algebra a).mul y z)) basis =
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.mul a y z) basis := rfl

/-- Composition transported to a chosen common endpoint label is ordinary
coefficient-algebra multiplication.  Keeping this transport in one lemma
avoids asking `simp` to guess the two intermediate label equalities. -/
private theorem cast_comp_coeff_at_common_label
    {X Y Z : Atom} (t : ZMod 8)
    (hX : X.label = t) (hY : Y.label = t) (hZ : Z.label = t)
    (f : AtomHom shiftedReal.D X Y) (g : AtomHom shiftedReal.D Y Z) :
    cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hX)
        ((AtomHom.comp f g).coeff (hX.trans hZ.symm)) =
      (shiftedReal.D.algebra t).mul
        (cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hY)
          (g.coeff (hY.trans hZ.symm)))
        (cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hX)
          (f.coeff (hX.trans hY.symm))) := by
  let F := fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier
  let hXY := hX.trans hY.symm
  let hYZ := hY.trans hZ.symm
  let hXZ := hX.trans hZ.symm
  have hp : hXZ = hXY.trans hYZ := Subsingleton.elim _ _
  change cast (congrArg F hX) ((AtomHom.comp f g).coeff hXZ) = _
  rw [show (AtomHom.comp f g).coeff hXZ =
      (AtomHom.comp f g).coeff (hXY.trans hYZ) by
        exact congrArg (fun h => (AtomHom.comp f g).coeff h) hp]
  rw [AtomHom.coeff_comp f g hXY hYZ]
  rw [cast_algebra_mul_of_label_eq shiftedReal.D hX]
  congr 1
  rw [cast_cast_eq]

/-- Three composable atomic coefficients transported to one endpoint label
multiply in diagrammatic order, namely `h * (g * f)`. -/
private theorem cast_triple_comp_coeff_at_common_label
    {W X Y Z : Atom} (t : ZMod 8)
    (hW : W.label = t) (hX : X.label = t)
    (hY : Y.label = t) (hZ : Z.label = t)
    (f : AtomHom shiftedReal.D W X)
    (g : AtomHom shiftedReal.D X Y)
    (h : AtomHom shiftedReal.D Y Z) :
    cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hW)
        ((AtomHom.comp (AtomHom.comp f g) h).coeff (hW.trans hZ.symm)) =
      (shiftedReal.D.algebra t).mul
        (cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hY)
          (h.coeff (hY.trans hZ.symm)))
        ((shiftedReal.D.algebra t).mul
          (cast (congrArg
            (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hX)
            (g.coeff (hX.trans hY.symm)))
          (cast (congrArg
            (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hW)
            (f.coeff (hW.trans hX.symm)))) := by
  rw [cast_comp_coeff_at_common_label t hW hY hZ]
  rw [cast_comp_coeff_at_common_label t hW hX hY]

/-- Canonical coordinate expansion in the executable coefficient basis. -/
private theorem coefficient_eq_sum_basis (a : ZMod 8)
    (x : RModCoordinate.Coeff a) :
    x = ∑ i : Fin (realRepDim a.val),
      RModCoordinate.Coeff.smul a (x i)
        (RawDCT.RealPChiKernel.coefficientBasis a i) := by
  funext k
  rw [Finset.sum_apply]
  change x k = ∑ i : Fin (realRepDim a.val),
    x i * (if k = i then 1 else 0)
  rw [Finset.sum_eq_single k]
  · simp
  · intro i _ hik
    simp [hik.symm]
  · simp

/-- Left multiplication distributes across a finite coordinate expansion. -/
private theorem coefficient_mul_sum_right (a : ZMod 8)
    (x : RModCoordinate.Coeff a) {I : Type} [Fintype I]
    (f : I → RModCoordinate.Coeff a) :
    RModCoordinate.Coeff.mul a x (∑ i, f i) =
      ∑ i, RModCoordinate.Coeff.mul a x (f i) := by
  let h := realComputableShiftedRawDCT.laws.D.algebra_laws a
  let L : RModCoordinate.Coeff a →+ RModCoordinate.Coeff a :=
    { toFun := RModCoordinate.Coeff.mul a x
      map_zero' := by
        funext k
        simp [RModCoordinate.Coeff.mul, RModCoordinate.Coeff.zero]
      map_add' := h.mul_add x }
  change L (∑ i, f i) = ∑ i, L (f i)
  exact map_sum L f Finset.univ

/-- Expand exactly the right input of one coefficient-algebra product in
the canonical basis.  The structured left-hand side makes this safe for
directed `rw`, unlike using `coefficient_eq_sum_basis` as a global simp
rule. -/
private theorem coefficient_mul_expand_right (a : ZMod 8)
    (x y : RModCoordinate.Coeff a) :
    RModCoordinate.Coeff.mul a x y =
      ∑ basis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.smul a (y basis)
            (RawDCT.RealPChiKernel.coefficientBasis a basis)) := by
  calc
    RModCoordinate.Coeff.mul a x y =
        RModCoordinate.Coeff.mul a x
          (∑ basis : Fin (realRepDim a.val),
            RModCoordinate.Coeff.smul a (y basis)
              (RawDCT.RealPChiKernel.coefficientBasis a basis)) :=
      congrArg (RModCoordinate.Coeff.mul a x)
        (coefficient_eq_sum_basis a y)
    _ = _ := coefficient_mul_sum_right a x _

/-- In a threefold product, expand only the first edge output, i.e. the
rightmost factor.  This introduces the basis feeding the middle edge. -/
private theorem coefficient_triple_expand_first (a : ZMod 8)
    (x y z : RModCoordinate.Coeff a) :
    RModCoordinate.Coeff.mul a x
        (RModCoordinate.Coeff.mul a y z) =
      ∑ basis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.mul a y
            (RModCoordinate.Coeff.smul a (z basis)
              (RawDCT.RealPChiKernel.coefficientBasis a basis))) := by
  calc
    RModCoordinate.Coeff.mul a x (RModCoordinate.Coeff.mul a y z) =
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.mul a y
            (∑ basis : Fin (realRepDim a.val),
              RModCoordinate.Coeff.smul a (z basis)
                (RawDCT.RealPChiKernel.coefficientBasis a basis))) :=
      congrArg (RModCoordinate.Coeff.mul a x)
        (congrArg (RModCoordinate.Coeff.mul a y)
          (coefficient_eq_sum_basis a z))
    _ = RModCoordinate.Coeff.mul a x
          (∑ basis : Fin (realRepDim a.val),
            RModCoordinate.Coeff.mul a y
              (RModCoordinate.Coeff.smul a (z basis)
                (RawDCT.RealPChiKernel.coefficientBasis a basis))) :=
      congrArg (RModCoordinate.Coeff.mul a x)
        (coefficient_mul_sum_right a y _)
    _ = _ := coefficient_mul_sum_right a x _

/-- After the first-edge basis is fixed, expand the resulting middle-edge
output.  This introduces the basis feeding the final edge without expanding
the final edge itself. -/
private theorem coefficient_triple_expand_middle (a : ZMod 8)
    (x y : RModCoordinate.Coeff a) (r : ℝ)
    (sourceBasis : Fin (realRepDim a.val)) :
    RModCoordinate.Coeff.mul a x
        (RModCoordinate.Coeff.mul a y
          (RModCoordinate.Coeff.smul a r
            (RawDCT.RealPChiKernel.coefficientBasis a sourceBasis))) =
      ∑ targetBasis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.smul a
            ((RModCoordinate.Coeff.mul a y
              (RModCoordinate.Coeff.smul a r
                (RawDCT.RealPChiKernel.coefficientBasis a sourceBasis)))
                  targetBasis)
            (RawDCT.RealPChiKernel.coefficientBasis a targetBasis)) := by
  let m := RModCoordinate.Coeff.mul a y
    (RModCoordinate.Coeff.smul a r
      (RawDCT.RealPChiKernel.coefficientBasis a sourceBasis))
  change RModCoordinate.Coeff.mul a x m = _
  calc
    RModCoordinate.Coeff.mul a x m =
        RModCoordinate.Coeff.mul a x
          (∑ targetBasis : Fin (realRepDim a.val),
            RModCoordinate.Coeff.smul a (m targetBasis)
              (RawDCT.RealPChiKernel.coefficientBasis a targetBasis)) :=
      congrArg (RModCoordinate.Coeff.mul a x)
        (coefficient_eq_sum_basis a m)
    _ = _ := coefficient_mul_sum_right a x _

/-- Read a finite sum through the proof-only coordinate observation. -/
private theorem observed_coefficient_sum_apply (a : ZMod 8)
    {I : Type} [Fintype I]
    (f : I → (shiftedReal.D.algebra a).carrier)
    (targetBasis : Fin (realRepDim a.val)) :
    observeCoefficient a (∑ i, f i) targetBasis =
      ∑ i, observeCoefficient a (f i) targetBasis := by
  rw [observeCoefficient_sum]
  exact Finset.sum_apply targetBasis Finset.univ _

/-- Expand the right input of an observed abstract product.  This combines
the definitional carrier observation with the directed coordinate expansion,
so later rewriting never has to unfold the shifted algebra. -/
private theorem observed_coefficient_mul_expand_right (a : ZMod 8)
    (x y : (shiftedReal.D.algebra a).carrier)
    (targetBasis : Fin (realRepDim a.val)) :
    observeCoefficient a ((shiftedReal.D.algebra a).mul x y) targetBasis =
      (∑ sourceBasis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a (observeCoefficient a x)
          (RModCoordinate.Coeff.smul a
            (observeCoefficient a y sourceBasis)
            (RawDCT.RealPChiKernel.coefficientBasis a
              (kernelIndex a sourceBasis))))
        targetBasis := by
  exact congrFun (coefficient_mul_expand_right a
    (observeCoefficient a x) (observeCoefficient a y)) targetBasis

/-- Directed first-edge expansion for an observed abstract threefold
product. -/
private theorem observed_coefficient_triple_expand_first (a : ZMod 8)
    (x y z : (shiftedReal.D.algebra a).carrier)
    (targetBasis : Fin (realRepDim a.val)) :
    observeCoefficient a
        ((shiftedReal.D.algebra a).mul x
          ((shiftedReal.D.algebra a).mul y z)) targetBasis =
      (∑ sourceBasis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a (observeCoefficient a x)
          (RModCoordinate.Coeff.mul a (observeCoefficient a y)
            (RModCoordinate.Coeff.smul a
              (observeCoefficient a z sourceBasis)
              (RawDCT.RealPChiKernel.coefficientBasis a
                (kernelIndex a sourceBasis)))))
        targetBasis := by
  exact congrFun (coefficient_triple_expand_first a
    (observeCoefficient a x) (observeCoefficient a y)
    (observeCoefficient a z)) targetBasis

/-- First-edge expansion with the public kernel basis index made explicit. -/
private theorem coefficient_triple_expand_first_kernel (a : ZMod 8)
    (x y z : RModCoordinate.Coeff a) :
    RModCoordinate.Coeff.mul a x (RModCoordinate.Coeff.mul a y z) =
      ∑ sourceBasis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.mul a y
            (RModCoordinate.Coeff.smul a (z sourceBasis)
              (RawDCT.RealPChiKernel.coefficientBasis a
                (kernelIndex a sourceBasis)))) := by
  exact coefficient_triple_expand_first a x y z

/-- Observe four nested finite sums of threefold products and perform only
the first directed basis expansion.  This is a generic algebraic adapter;
it does not inspect any route or coefficient table. -/
private theorem observed_four_sum_triple_expand_first (a : ZMod 8)
    {I J K L : Type} [Fintype I] [Fintype J] [Fintype K] [Fintype L]
    (x y z : I → J → K → L → (shiftedReal.D.algebra a).carrier)
    (targetBasis : Fin (realRepDim a.val)) :
    observeCoefficient a
        (∑ i, ∑ j, ∑ k, ∑ l,
          (shiftedReal.D.algebra a).mul (x i j k l)
            ((shiftedReal.D.algebra a).mul (y i j k l) (z i j k l)))
        targetBasis =
      ∑ i, ∑ j, ∑ k, ∑ l,
        ∑ sourceBasis : Fin (realRepDim a.val),
          RModCoordinate.Coeff.mul a (observeCoefficient a (x i j k l))
            (RModCoordinate.Coeff.mul a
              (observeCoefficient a (y i j k l))
              (RModCoordinate.Coeff.smul a
                (observeCoefficient a (z i j k l) sourceBasis)
                (RawDCT.RealPChiKernel.coefficientBasis a
                  (kernelIndex a sourceBasis)))) targetBasis := by
  rw [observed_coefficient_sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [observed_coefficient_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [observed_coefficient_sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [observed_coefficient_sum_apply]
  apply Finset.sum_congr rfl
  intro l _
  rw [observed_coefficient_triple_expand_first]
  rw [Finset.sum_apply]

/-- The middle-edge expansion with all public-kernel basis indices transported
explicitly from the underlying coordinate index type. -/
private theorem coefficient_triple_expand_middle_kernel (a : ZMod 8)
    (x y : RModCoordinate.Coeff a) (r : ℝ)
    (sourceBasis : Fin (realRepDim a.val)) :
    RModCoordinate.Coeff.mul a x
        (RModCoordinate.Coeff.mul a y
          (RModCoordinate.Coeff.smul a r
            (RawDCT.RealPChiKernel.coefficientBasis a
              (kernelIndex a sourceBasis)))) =
      ∑ targetBasis : Fin (realRepDim a.val),
        RModCoordinate.Coeff.mul a x
          (RModCoordinate.Coeff.smul a
            ((RModCoordinate.Coeff.mul a y
              (RModCoordinate.Coeff.smul a r
                (RawDCT.RealPChiKernel.coefficientBasis a
                  (kernelIndex a sourceBasis)))) targetBasis)
            (RawDCT.RealPChiKernel.coefficientBasis a
              (kernelIndex a targetBasis))) := by
  exact coefficient_triple_expand_middle a x y r (kernelIndex a sourceBasis)

/-! ## Whisker coordinate splices for the three-edge route

The two outer edges of the top pentagon route are whiskers: a connector
coefficient acts on one slot of a fusion column while the other slot holds
the unit.  The next two lemmas expand exactly that acting coefficient in the
canonical basis, reading the remaining matrix through the saved integer
left- and right-slot fusion kernels.  No table is recomputed: both proofs
end in `fusionLeftSlotCoeff_cast` / `fusionRightSlotCoeff_cast`. -/

set_option backward.isDefEq.respectTransparency false in
/-- Observed left whisker: the acting coefficient expands in the canonical
basis against the saved left-slot fusion kernel at the unit column. -/
private theorem observed_leftWhisker_apply (A B : ZMod 8)
    (target source : shiftedReal.C.Index A B)
    (x : (shiftedReal.D.algebra A).carrier)
    (tgtBasis : Fin (realRepDim (A + B).val)) :
    observeCoefficient (A + B)
        (rawReal.C.leftCoeff A B target source x
          (rawReal.D.algebra B).one) tgtBasis =
      ∑ acting : Fin (realRepDim A.val),
        observeCoefficient A x acting *
          ((RawDCT.RealPChiKernel.fusionLeftSlotCoeff A B
            acting.val target.val tgtBasis.val source.val
            (RawDCT.RealPChiKernel.coefficientUnitIndex (A + B)).val
            : ℤ) : ℝ) := by
    change RModCoordinate.FusionTable.Index A B at target
    change RModCoordinate.FusionTable.Index A B at source
    change
      RModCoordinate.FusionTable.fusionCoefficient A B target source
        (observeCoefficient A x) (RModCoordinate.Coeff.one B) tgtBasis = _
    let L : RModCoordinate.Coeff A →+ RModCoordinate.Coeff (A + B) :=
      { toFun := fun v =>
          RModCoordinate.FusionTable.fusionCoefficient A B target source v
            (RModCoordinate.Coeff.one B)
        map_zero' :=
          RawDCT.FusionTableLaws.fusionCoefficient_zero_left A B
            target source (RModCoordinate.Coeff.one B)
        map_add' := fun v w =>
          RawDCT.FusionTableLaws.fusionCoefficient_add_left A B
            target source v w (RModCoordinate.Coeff.one B) }
    conv_lhs => rw [coefficient_eq_sum_basis A (observeCoefficient A x)]
    change (L (∑ acting : Fin (realRepDim A.val),
      RModCoordinate.Coeff.smul A (observeCoefficient A x acting)
        (RawDCT.RealPChiKernel.coefficientBasis A acting))) tgtBasis = _
    rw [map_sum L _ Finset.univ, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro acting _
    change
      RModCoordinate.FusionTable.fusionCoefficient A B target source
        (RModCoordinate.Coeff.smul A (observeCoefficient A x acting)
          (RawDCT.RealPChiKernel.coefficientBasis A acting))
        (RModCoordinate.Coeff.one B) tgtBasis = _
    rw [RawDCT.FusionTableLaws.fusionCoefficient_smul_left]
    have htab := RawDCT.RealPChiKernel.fusionLeftSlotCoeff_cast A B
      (kernelIndex A acting) target source
      (kernelIndex (A + B) tgtBasis)
      (RawDCT.RealPChiKernel.coefficientUnitIndex (A + B))
    rw [RawDCT.RealPChiRouteBridge.coefficientBasis_unit (A + B),
      RModCoordinate.Coeff.mul_one,
      RawDCT.RealPChiRouteBridge.coefficientBasis_unit B] at htab
    change observeCoefficient A x acting *
      RModCoordinate.FusionTable.fusionCoefficient A B target source
        (RawDCT.RealPChiKernel.coefficientBasis A
          (kernelIndex A acting))
        (RModCoordinate.Coeff.one B) (kernelIndex (A + B) tgtBasis) = _
    exact congrArg
      (fun t => observeCoefficient A x acting * t) htab.symm

set_option backward.isDefEq.respectTransparency false in
/-- Observed right whisker against one source basis column: the acting
coefficient expands in the canonical basis against the saved right-slot
fusion kernel. -/
private theorem observed_rightWhisker_mul_basis (A B : ZMod 8)
    (target source : shiftedReal.C.Index A B)
    (y : (shiftedReal.D.algebra B).carrier)
    (srcIdx : Fin (RawDCT.RealPChiKernel.coefficientRank (A + B)))
    (tgtBasis : Fin (realRepDim (A + B).val)) :
    RModCoordinate.Coeff.mul (A + B)
        (observeCoefficient (A + B)
          (rawReal.C.leftCoeff A B target source
            (rawReal.D.algebra A).one y))
        (RawDCT.RealPChiKernel.coefficientBasis (A + B) srcIdx)
        tgtBasis =
      ∑ acting : Fin (realRepDim B.val),
        observeCoefficient B y acting *
          ((RawDCT.RealPChiKernel.fusionRightSlotCoeff A B
            acting.val target.val tgtBasis.val source.val
            srcIdx.val : ℤ) : ℝ) := by
    change RModCoordinate.FusionTable.Index A B at target
    change RModCoordinate.FusionTable.Index A B at source
    let hlaw := realComputableShiftedRawDCT.laws.D.algebra_laws (A + B)
    let R : RModCoordinate.Coeff B →+ RModCoordinate.Coeff (A + B) :=
      { toFun := fun v =>
          RModCoordinate.Coeff.mul (A + B)
            (RModCoordinate.FusionTable.fusionCoefficient A B target source
              (RModCoordinate.Coeff.one A) v)
            (RawDCT.RealPChiKernel.coefficientBasis (A + B)
              srcIdx)
        map_zero' := by
          show RModCoordinate.Coeff.mul (A + B)
              (RModCoordinate.FusionTable.fusionCoefficient A B
                target source (RModCoordinate.Coeff.one A)
                (RModCoordinate.Coeff.zero B))
              (RawDCT.RealPChiKernel.coefficientBasis (A + B)
                srcIdx) = 0
          rw [RawDCT.FusionTableLaws.fusionCoefficient_zero_right]
          funext k
          simp [RModCoordinate.Coeff.mul, RModCoordinate.Coeff.zero]
        map_add' := fun v w => by
          show RModCoordinate.Coeff.mul (A + B)
              (RModCoordinate.FusionTable.fusionCoefficient A B
                target source (RModCoordinate.Coeff.one A)
                (RModCoordinate.Coeff.add B v w))
              (RawDCT.RealPChiKernel.coefficientBasis (A + B)
                srcIdx) = _
          rw [RawDCT.FusionTableLaws.fusionCoefficient_add_right]
          exact hlaw.add_mul _ _ _ }
    change (R (observeCoefficient B y)) tgtBasis = _
    conv_lhs => rw [coefficient_eq_sum_basis B (observeCoefficient B y)]
    rw [map_sum R _ Finset.univ, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro acting _
    change RModCoordinate.Coeff.mul (A + B)
        (RModCoordinate.FusionTable.fusionCoefficient A B target source
          (RModCoordinate.Coeff.one A)
          (RModCoordinate.Coeff.smul B (observeCoefficient B y acting)
            (RawDCT.RealPChiKernel.coefficientBasis B acting)))
        (RawDCT.RealPChiKernel.coefficientBasis (A + B)
          srcIdx) tgtBasis = _
    rw [RawDCT.FusionTableLaws.fusionCoefficient_smul_right,
      RModCoordinate.Coeff.smul_mul, RModCoordinate.Coeff.smul_apply]
    have htab := RawDCT.RealPChiKernel.fusionRightSlotCoeff_cast A B
      (kernelIndex B acting) target source
      (kernelIndex (A + B) tgtBasis) srcIdx
    rw [RawDCT.RealPChiRouteBridge.coefficientBasis_unit] at htab
    exact congrArg (fun r =>
      observeCoefficient B y acting * r) htab.symm

set_option backward.isDefEq.respectTransparency false in
/-- Full coordinate form of the observed middle factor of the three-edge
route: label transport, sign extraction, and the mul-basis connector bridge
in one step. -/
private theorem observed_topMiddle_mul_basis (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (srcB tgtB : Fin (realRepDim
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label).val)) :
    RModCoordinate.Coeff.mul
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label)
        (observeCoefficient
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              (congrArg (fun q => q + (Z.atom l).label)
                (_root_.add_assoc (W.atom i).label
                  (X.atom j).label (Y.atom k).label).symm))
            ((shiftedReal.D.algebra
              ((W.atom i).label +
                ((X.atom j).label + (Y.atom k).label) +
                (Z.atom l).label)).smul
              (RawDCT.paritySign
                (shiftedReal.C.rowParity (W.atom i).label
                    ((X.atom j).label + (Y.atom k).label) a_bc *
                  (Z.atom l).shift))
              (Associator.homCoefficient shiftedReal
                (W.atom i).label
                ((X.atom j).label + (Y.atom k).label)
                (Z.atom l).label a_bc
                (Associator.castIndex shiftedReal
                  (_root_.add_assoc (W.atom i).label
                    (X.atom j).label (Y.atom k).label) rfl rowLast)
                bc_d a_bcd))))
        (RawDCT.RealPChiKernel.coefficientBasis
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label)
          (kernelIndex
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
              (Z.atom l).label) srcB)) tgtB =
      RawDCT.paritySign
          (shiftedReal.C.rowParity (W.atom i).label
              ((X.atom j).label + (Y.atom k).label) a_bc *
            (Z.atom l).shift) *
        ((rightRouteFrameSign rawReal.C realComputableNuBeta.data
              (W.atom i).label ((X.atom j).label + (Y.atom k).label)
              (Z.atom l).label
              (rawIndexOfShifted
                ((X.atom j).label + (Y.atom k).label) (Z.atom l).label
                bc_d) *
            (↑(shiftBeta realComputableNuBeta.data
              (W.atom i).label ((X.atom j).label + (Y.atom k).label)
              (Z.atom l).label)⁻¹ : ℝ) *
            leftRouteFrameSign rawReal.C realComputableNuBeta.data
              (W.atom i).label ((X.atom j).label + (Y.atom k).label)
              (Z.atom l).label
              (rawIndexOfShifted (W.atom i).label
                ((X.atom j).label + (Y.atom k).label) a_bc)) *
          ((RawDCT.RealPChiKernel.connectorLinearCoeff
            (W.atom i).label ((X.atom j).label + (Y.atom k).label)
            (Z.atom l).label
            bc_d.val a_bcd.val a_bc.val rowLast.val
            tgtB.val srcB.val : ℤ) : ℝ)) := by
    rw [observed_cast_algebra_mul_basis_apply
      (congrArg (fun q => q + (Z.atom l).label)
        (_root_.add_assoc (W.atom i).label
          (X.atom j).label (Y.atom k).label).symm)]
    rw [observeCoefficient_smul, RModCoordinate.Coeff.smul_mul,
      RModCoordinate.Coeff.smul_apply]
    rw [observed_realShiftedHomCoefficient_mul_basis_eq]
    rw [realShiftedHomCoefficient_mul_basis_public]
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast,
      kernelIndex_val, castIndex_val]

set_option backward.isDefEq.respectTransparency false in
/-- Full coordinate form of the observed final factor of the three-edge
route: label transport, the two sign extractions, and the right-whisker
basis expansion in one step. -/
private theorem observed_topFinal_mul_basis (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (srcB tgtB : Fin (realRepDim
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label).val)) :
    RModCoordinate.Coeff.mul
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label)
        (observeCoefficient
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              (show (W.atom i).label + (X.atom j).label + (Y.atom k).label +
                    (Z.atom l).label =
                  (W.atom i).label +
                    ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
                  by ac_rfl).symm)
            ((shiftedReal.D.algebra ((W.atom i).label +
              ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))).smul
              (RawDCT.paritySign
                (shiftNu realComputableNuBeta.data (W.atom i).label
                  ((X.atom j).label + (Y.atom k).label + (Z.atom l).label) *
                  (rawReal.T.parity
                      (X.atom j).label (Y.atom k).label (Z.atom l).label +
                    rawRowParityOfShifted
                      (X.atom j).label (Y.atom k).label bc +
                    rawRowParityOfShifted
                      ((X.atom j).label + (Y.atom k).label)
                      (Z.atom l).label bc_d +
                    rawRowParityOfShifted
                      (Y.atom k).label (Z.atom l).label cd +
                    rawRowParityOfShifted (X.atom j).label
                      ((Y.atom k).label + (Z.atom l).label) bcd)))
              ((shiftedReal.D.algebra ((W.atom i).label +
                ((X.atom j).label + (Y.atom k).label +
                  (Z.atom l).label))).smul
                (RawDCT.paritySign
                  (shiftedReal.C.rowParity
                      (X.atom j).label (Y.atom k).label bc *
                    (Z.atom l).shift))
                (rawReal.C.leftCoeff (W.atom i).label
                  ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
                  targetABCD a_bcd
                  (rawReal.D.algebra (W.atom i).label).one
                  (Associator.homCoefficient shiftedReal
                    (X.atom j).label (Y.atom k).label (Z.atom l).label
                    bc bc_d cd bcd))))))
        (RawDCT.RealPChiKernel.coefficientBasis
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label)
          (kernelIndex
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
              (Z.atom l).label) srcB)) tgtB =
      RawDCT.paritySign
          (shiftNu realComputableNuBeta.data (W.atom i).label
            ((X.atom j).label + (Y.atom k).label + (Z.atom l).label) *
            (rawReal.T.parity
                (X.atom j).label (Y.atom k).label (Z.atom l).label +
              rawRowParityOfShifted (X.atom j).label (Y.atom k).label bc +
              rawRowParityOfShifted
                ((X.atom j).label + (Y.atom k).label) (Z.atom l).label
                bc_d +
              rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd +
              rawRowParityOfShifted (X.atom j).label
                ((Y.atom k).label + (Z.atom l).label) bcd)) *
        (RawDCT.paritySign
            (shiftedReal.C.rowParity
                (X.atom j).label (Y.atom k).label bc *
              (Z.atom l).shift) *
          ∑ acting : Fin (realRepDim
            ((X.atom j).label + (Y.atom k).label + (Z.atom l).label).val),
            observeCoefficient
                ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
                (Associator.homCoefficient shiftedReal
                  (X.atom j).label (Y.atom k).label (Z.atom l).label
                  bc bc_d cd bcd) acting *
              ((RawDCT.RealPChiKernel.fusionRightSlotCoeff
                (W.atom i).label
                ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
                acting.val targetABCD.val tgtB.val a_bcd.val
                srcB.val : ℤ) : ℝ)) := by
    rw [observed_cast_algebra_mul_basis_apply
      (show (W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label =
          (W.atom i).label +
            ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
          by ac_rfl).symm]
    rw [observeCoefficient_smul, RModCoordinate.Coeff.smul_mul,
      RModCoordinate.Coeff.smul_apply]
    rw [observeCoefficient_smul, RModCoordinate.Coeff.smul_mul,
      RModCoordinate.Coeff.smul_apply]
    rw [observed_rightWhisker_mul_basis]
    simp only [finCongr_symm, finCongr_apply, Fin.val_cast,
      kernelIndex_val]

/-- Reindex both binders of a rectangular finite sum by explicit
equivalences.  This proof-only helper keeps dependent slot enumeration out of
the matrix coefficient formulas. -/
private theorem sum_sum_comp_equiv
    {I I' J J' M : Type*} [Fintype I] [Fintype I']
    [Fintype J] [Fintype J'] [AddCommMonoid M]
    (eI : I ≃ I') (eJ : J ≃ J') (f : I' → J' → M) :
    (∑ i' : I', ∑ j' : J', f i' j') =
      ∑ i : I, ∑ j : J, f (eI i) (eJ j) := by
  rw [← eI.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  rw [← eJ.sum_comp]

/-- A bottom-route matrix coefficient is the sum over its single
intermediate tensor slot.  This is only a change of finite indexing. -/
private theorem bottom_coeff_as_slot_sum (W X Y Z : Obj)
    (pS : Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size)
    (pT : Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size)
    (hLabel :
      ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label =
        ((tensorObj W (tensorObj X (tensorObj Y Z))).atom pT).label) :
    ((bottomRoute W X Y Z pS pT).coeff hLabel) =
      ∑ qM : Tensor.Slot shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z),
        (AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj (tensorObj W X) Y) Z).get pS) qM)
          (RealAssociator.homEntry W X (tensorObj Y Z) qM
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))).coeff
            hLabel := by
  letI : Fact (SuperAlgebraLaws
      (shiftedReal.D.algebra
        ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  unfold bottomRoute
  rw [RealAssociatorLaws.realComp_coeff_as_sum]
  change (∑ j : Fin (tensorObj (tensorObj W X) (tensorObj Y Z)).size,
      (AtomHom.comp
        (RealAssociator.homEntry (tensorObj W X) Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (tensorObj (tensorObj W X) Y) Z).get pS)
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (tensorObj W X) (tensorObj Y Z)).get j))
        (RealAssociator.homEntry W X (tensorObj Y Z)
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (tensorObj W X) (tensorObj Y Z)).get j)
          ((Tensor.slots shiftedReal.D shiftedReal.C W
            (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel) = _
  let e := RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
    (tensorObj W X) (tensorObj Y Z)
  let F : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z) →
      RModCoordinate.Coeff
        (((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label) :=
    fun qM =>
      (AtomHom.comp
        (RealAssociator.homEntry (tensorObj W X) Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (tensorObj (tensorObj W X) Y) Z).get pS) qM)
        (RealAssociator.homEntry W X (tensorObj Y Z) qM
          ((Tensor.slots shiftedReal.D shiftedReal.C W
            (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel
  change (∑ j : Fin (tensorObj (tensorObj W X) (tensorObj Y Z)).size,
      F (e j)) = ∑ qM, F qM
  exact e.sum_comp F

/-- A top-route matrix coefficient is the double sum over the two
intermediate tensor slots.  This only unfolds matrix composition and changes
the two finite-list indices to the corresponding dependent slot types. -/
private theorem top_coeff_as_slot_sum (W X Y Z : Obj)
    (pS : Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size)
    (pT : Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size)
    (hLabel :
      ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label =
        ((tensorObj W (tensorObj X (tensorObj Y Z))).atom pT).label) :
    ((topRoute W X Y Z pS pT).coeff hLabel) =
      ∑ q₁ : Tensor.Slot shiftedReal.D shiftedReal.C
          (tensorObj W (tensorObj X Y)) Z,
      ∑ q₂ : Tensor.Slot shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z),
        (AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj (tensorObj W X) Y) Z).get pS) q₁)
            (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel := by
  letI : Fact (SuperAlgebraLaws
      (shiftedReal.D.algebra
        ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  unfold topRoute
  rw [RealAssociatorLaws.realComp_coeff_as_sum]
  let q₁Count := (tensorObj (tensorObj W (tensorObj X Y)) Z).size
  let q₂Count := (tensorObj W (tensorObj (tensorObj X Y) Z)).size
  change (∑ q₂ : Fin q₂Count,
      (AtomHom.comp
        ((Hom.comp
          (Tensor.hom shiftedReal.D shiftedReal.C
            (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z))
          (RealAssociator.hom W (tensorObj X Y) Z)) pS q₂)
        (Tensor.entry shiftedReal.D shiftedReal.C
          (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
          ((Tensor.slots shiftedReal.D shiftedReal.C W
            (tensorObj (tensorObj X Y) Z)).get q₂)
          ((Tensor.slots shiftedReal.D shiftedReal.C W
            (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel) = _
  calc
    _ = ∑ q₂ : Fin q₂Count, ∑ q₁ : Fin q₁Count,
        (AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj (tensorObj W X) Y) Z).get pS)
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj W (tensorObj X Y)) Z).get q₁))
            (RealAssociator.homEntry W (tensorObj X Y) Z
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj W (tensorObj X Y)) Z).get q₁)
              ((Tensor.slots shiftedReal.D shiftedReal.C W
                (tensorObj (tensorObj X Y) Z)).get q₂)))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z)).get q₂)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel := by
      apply Finset.sum_congr rfl
      intro q₂ _
      change (AtomHom.comp
          (AtomHom.finSum q₁Count (fun q₁ =>
            AtomHom.comp
              (Tensor.entry shiftedReal.D shiftedReal.C
                (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj (tensorObj W X) Y) Z).get pS)
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get q₁))
              (RealAssociator.homEntry W (tensorObj X Y) Z
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get q₁)
                ((Tensor.slots shiftedReal.D shiftedReal.C W
                  (tensorObj (tensorObj X Y) Z)).get q₂))))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z)).get q₂)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel = _
      rw [AtomHom.finSum_comp realComputableShiftedRawDCT.laws.D]
      rw [atomHom_finSum_coeff]
    _ = ∑ q₁ : Fin q₁Count, ∑ q₂ : Fin q₂Count,
        (AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj (tensorObj W X) Y) Z).get pS)
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj W (tensorObj X Y)) Z).get q₁))
            (RealAssociator.homEntry W (tensorObj X Y) Z
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj W (tensorObj X Y)) Z).get q₁)
              ((Tensor.slots shiftedReal.D shiftedReal.C W
                (tensorObj (tensorObj X Y) Z)).get q₂)))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z)).get q₂)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel := by
      rw [Finset.sum_comm]
    _ = _ := by
      let e₁ := RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
        (tensorObj W (tensorObj X Y)) Z
      let e₂ := RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
        W (tensorObj (tensorObj X Y) Z)
      let F :
          Tensor.Slot shiftedReal.D shiftedReal.C
              (tensorObj W (tensorObj X Y)) Z →
            Tensor.Slot shiftedReal.D shiftedReal.C W
                (tensorObj (tensorObj X Y) Z) →
              RModCoordinate.Coeff
                (((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label) :=
        fun
          (q₁ : Tensor.Slot shiftedReal.D shiftedReal.C
            (tensorObj W (tensorObj X Y)) Z)
          (q₂ : Tensor.Slot shiftedReal.D shiftedReal.C W
            (tensorObj (tensorObj X Y) Z)) =>
        (AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj (tensorObj W X) Y) Z).get pS) q₁)
            (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))).coeff hLabel
      change (∑ q₁ : Fin q₁Count, ∑ q₂ : Fin q₂Count,
          F (e₁ q₁) (e₂ q₂)) = ∑ q₁, ∑ q₂, F q₁ q₂
      exact (sum_sum_comp_equiv e₁ e₂ F).symm

/-! ### The unique object-position block on the bottom route -/

private def binarySlot (X Y : Obj) (i : Fin X.size) (j : Fin Y.size)
    (r : shiftedReal.C.Index (X.atom i).label (Y.atom j).label) :
    Tensor.Slot shiftedReal.D shiftedReal.C X Y :=
  ⟨i, j, r⟩

private theorem binarySlot_position_label (X Y : Obj)
    (i : Fin X.size) (j : Fin Y.size)
    (r : shiftedReal.C.Index (X.atom i).label (Y.atom j).label) :
    ((tensorObj X Y).atom
      (RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C X Y
        (binarySlot X Y i j r))).label =
      (X.atom i).label + (Y.atom j).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
    ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      (RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C X Y
        (binarySlot X Y i j r)))).label = _
  rw [RealAssociatorLaws.get_slotPosition]
  rfl

private def bottomMiddleSlot (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z) := by
  let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    W X (binarySlot W X i j ab)
  let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    Y Z (binarySlot Y Z k l cd)
  let hAB := binarySlot_position_label W X i j ab
  let hCD := binarySlot_position_label Y Z k l cd
  exact ⟨pAB, pCD,
    Associator.castIndex shiftedReal hAB.symm hCD.symm rowABCD⟩

/-- The middle bottom slot is, equivalently, the direct pair of the two
binary slot positions with the outer row transported at both endpoints.
This form is used only to reindex the finite middle-row sum. -/
private theorem bottomMiddleSlot_eq_explicit (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      W X (binarySlot W X i j ab)
    let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      Y Z (binarySlot Y Z k l cd)
    let hAB := binarySlot_position_label W X i j ab
    let hCD := binarySlot_position_label Y Z k l cd
    bottomMiddleSlot W X Y Z i j k l ab cd rowABCD =
      (show Tensor.Slot shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z) from
        ⟨pAB, pCD,
          Associator.castIndex shiftedReal hAB.symm hCD.symm rowABCD⟩) := by
  rfl

@[simp] private theorem bottomMiddleSlot_left (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD).left =
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C W X
        (binarySlot W X i j ab) := by
  rfl

@[simp] private theorem bottomMiddleSlot_right (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD).right =
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C Y Z
        (binarySlot Y Z k l cd) := by
  rfl

private theorem bottomMiddleSlot_label (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z)
      (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD)).label =
        (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label := by
  change ((tensorObj W X).atom
      (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD).left).label +
    ((tensorObj Y Z).atom
      (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD).right).label = _
  rw [bottomMiddleSlot_left, bottomMiddleSlot_right,
    binarySlot_position_label, binarySlot_position_label]
  ac_rfl

private theorem quadLeftSlot_firstPosition (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    ((Tensor.slots shiftedReal.D shiftedReal.C (tensorObj W X) Y).get
      (quadLeftSlot W X Y Z i j k l ab abc abcd).left).left =
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C W X
        (binarySlot W X i j ab) := by
  rw [quadLeftSlot_inner,
    show (RealAssociatorLaws.leftRouteSlot W X Y i j k ab abc).left =
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C W X
        (binarySlot W X i j ab) by rfl]

private theorem quadRightSlot_lastPosition (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    ((Tensor.slots shiftedReal.D shiftedReal.C X (tensorObj Y Z)).get
      (quadRightSlot W X Y Z i j k l cd bcd abcd).right).right =
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C Y Z
        (binarySlot Y Z k l cd) := by
  rw [quadRightSlot_inner,
    show (RealAssociatorLaws.rightRouteSlot X Y Z j k l cd bcd).right =
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C Y Z
        (binarySlot Y Z k l cd) by rfl]

private def quadSource {W X Y Z : Obj}
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    RawDCT.RealPChiKernel.QuadSource (W.atom i).label (X.atom j).label
      (Y.atom k).label (Z.atom l).label :=
  ((ab, abc),
    (abcd, RawDCT.RealPChiKernel.coefficientUnitIndex
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label)))

private theorem quadTotalAssoc (a b c d : ZMod 8) :
    a + b + c + d = a + (b + c + d) := by
  ac_rfl

/-- Reassociating the total label only transports the coefficient-basis
type; it leaves the stored basis number unchanged. -/
@[simp] private theorem coefficientBasis_cast_val
    {a b : ZMod 8} (h : a = b)
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank a)) :
    (cast (congrArg
      (fun t => Fin (RawDCT.RealPChiKernel.coefficientRank t)) h)
      basis).val = basis.val := by
  subst b
  rfl

private def quadTarget {W X Y Z : Obj}
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label))) :
    RawDCT.RealPChiKernel.QuadTarget (W.atom i).label (X.atom j).label
      (Y.atom k).label (Z.atom l).label :=
  ((cd, bcd), (abcd,
    cast (congrArg (fun a => Fin
      (RawDCT.RealPChiKernel.coefficientRank a))
      (quadTotalAssoc (W.atom i).label (X.atom j).label
        (Y.atom k).label (Z.atom l).label)) basis))

theorem quadRouteLabelEq (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z
      (quadLeftSlot W X Y Z i j k l ab abc sourceABCD)).label =
    (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))
      (quadRightSlot W X Y Z i j k l cd bcd targetABCD)).label := by
  rw [quadLeftSlot_label, quadRightSlot_label]
  ac_rfl

/-- One bottom-route summand, transported to the canonical four-object
label, is the product of the two individually transported associator
coefficients.  Equality-proof choices are discharged by proof irrelevance. -/
private theorem cast_bottom_comp_coeff_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
    let hM := bottomMiddleSlot_label W X Y Z i j k l ab cd rowABCD
    let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z)) qT).label = t :=
      (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
        (by
          exact (_root_.add_assoc (W.atom i).label (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label)).symm.trans
              (_root_.add_assoc
                ((W.atom i).label + (X.atom j).label)
                (Y.atom k).label (Z.atom l).label).symm)
    cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hS)
        ((AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z qS qM)
          (RealAssociator.homEntry W X (tensorObj Y Z) qM qT)).coeff
            (quadRouteLabelEq W X Y Z i j k l
              ab abc sourceABCD cd bcd targetABCD)) =
      (shiftedReal.D.algebra t).mul
        (cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hM)
          ((RealAssociator.homEntry W X (tensorObj Y Z) qM qT).coeff
            (hM.trans hT.symm)))
        (cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hS)
          ((RealAssociator.homEntry (tensorObj W X) Y Z qS qM).coeff
            (hS.trans hM.symm))) := by
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
  let hM := bottomMiddleSlot_label W X Y Z i j k l ab cd rowABCD
  let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) qT).label = t :=
    (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
      (by
        exact (_root_.add_assoc (W.atom i).label (X.atom j).label
          ((Y.atom k).label + (Z.atom l).label)).symm.trans
            (_root_.add_assoc
              ((W.atom i).label + (X.atom j).label)
              (Y.atom k).label (Z.atom l).label).symm)
  have hp : quadRouteLabelEq W X Y Z i j k l
      ab abc sourceABCD cd bcd targetABCD = hS.trans hT.symm :=
    Subsingleton.elim _ _
  rw [hp]
  exact cast_comp_coeff_at_common_label t hS hM hT
    (RealAssociator.homEntry (tensorObj W X) Y Z qS qM)
    (RealAssociator.homEntry W X (tensorObj Y Z) qM qT)

/-- Once the four exterior object positions are fixed, the bottom-route
slot sum has only its middle fusion row left. -/
private theorem bottom_quad_slot_sum_eq_row_sum (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (hSlot := quadRouteLabelEq W X Y Z
      i j k l ab abc sourceABCD cd bcd targetABCD) :
    let qS := quadLeftSlot W X Y Z
      i j k l ab abc sourceABCD
    let qT := quadRightSlot W X Y Z
      i j k l cd bcd targetABCD
    (∑ qM : Tensor.Slot shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z),
        (AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z qS qM)
          (RealAssociator.homEntry W X (tensorObj Y Z) qM qT)).coeff
            hSlot) =
      ∑ rowABCD : shiftedReal.C.Index
          ((W.atom i).label + (X.atom j).label)
          ((Y.atom k).label + (Z.atom l).label),
        (AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z qS
            (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD))
          (RealAssociator.homEntry W X (tensorObj Y Z)
            (bottomMiddleSlot W X Y Z i j k l ab cd rowABCD) qT)).coeff
              hSlot := by
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let F := fun qM : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z) =>
    (AtomHom.comp
      (RealAssociator.homEntry (tensorObj W X) Y Z qS qM)
      (RealAssociator.homEntry W X (tensorObj Y Z) qM qT)).coeff
        (quadRouteLabelEq W X Y Z
          i j k l ab abc sourceABCD cd bcd targetABCD)
  rw [RealAssociatorLaws.sum_slots (tensorObj W X) (tensorObj Y Z) F]
  let pAB : Fin (tensorObj W X).size :=
    RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      W X (binarySlot W X i j ab)
  rw [Fintype.sum_eq_single pAB]
  · let pCD : Fin (tensorObj Y Z).size :=
      RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
        Y Z (binarySlot Y Z k l cd)
    rw [Fintype.sum_eq_single pCD]
    · let hAB := binarySlot_position_label W X i j ab
      let hCD := binarySlot_position_label Y Z k l cd
      let e : shiftedReal.C.Index
          ((W.atom i).label + (X.atom j).label)
          ((Y.atom k).label + (Z.atom l).label) ≃
          shiftedReal.C.Index ((tensorObj W X).atom pAB).label
            ((tensorObj Y Z).atom pCD).label :=
        Equiv.cast (congrArg₂ shiftedReal.C.Index hAB.symm hCD.symm)
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro row _
      apply congrArg F
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Sigma.ext rfl
      apply heq_of_eq
      change Associator.castIndex shiftedReal hAB.symm hCD.symm row =
        Associator.castIndex shiftedReal hAB.symm hCD.symm row
      rfl
    · intro other hne
      apply Finset.sum_eq_zero
      intro row _
      have hRight : other ≠
          ((Tensor.slots shiftedReal.D shiftedReal.C X (tensorObj Y Z)).get
            qT.right).right := by
        rw [quadRightSlot_lastPosition W X Y Z i j k l cd bcd targetABCD]
        exact hne
      have hz := RealAssociatorNaturality.realHomEntry_zero_of_right_ne
        W X (tensorObj Y Z)
        (show Tensor.Slot shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z) from ⟨pAB, other, row⟩)
        qT hRight
      change F ⟨pAB, other, row⟩ = 0
      unfold F
      rw [hz, AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
        AtomHom.coeff_zero]
      rfl
  · intro other hne
    apply Finset.sum_eq_zero
    intro pCD _
    apply Finset.sum_eq_zero
    intro row _
    have hLeft :
        ((Tensor.slots shiftedReal.D shiftedReal.C (tensorObj W X) Y).get
          qS.left).left ≠ other := by
      rw [quadLeftSlot_firstPosition W X Y Z i j k l
        ab abc sourceABCD]
      exact hne.symm
    have hz := RealAssociatorNaturality.realHomEntry_zero_of_left_ne
      (tensorObj W X) Y Z qS
      (show Tensor.Slot shiftedReal.D shiftedReal.C
        (tensorObj W X) (tensorObj Y Z) from ⟨other, pCD, row⟩)
      hLeft
    change F ⟨other, pCD, row⟩ = 0
    unfold F
    rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D,
      AtomHom.coeff_zero]
    rfl

/-! ### Matching bottom entries with explicit ternary routes -/

private theorem quadLeftSlot_as_outerLeftRoute (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (abcd : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      W X (binarySlot W X i j ab)
    let hAB := binarySlot_position_label W X i j ab
    let abc' := Associator.castIndex shiftedReal hAB.symm rfl abc
    let abcd' := Associator.castIndex shiftedReal
      (congrArg (fun x => x + (Y.atom k).label) hAB).symm rfl abcd
    quadLeftSlot W X Y Z i j k l ab abc abcd =
      RealAssociatorLaws.leftRouteSlot (tensorObj W X) Y Z
        pAB k l abc' abcd' := by
  dsimp only
  let qInner := RealAssociatorLaws.leftRouteSlot W X Y i j k ab abc
  let outer := Associator.castIndex shiftedReal
    (RealAssociatorLaws.leftRouteSlot_label W X Y i j k ab abc).symm
    rfl abcd
  let c₁ : RealAssociatorLaws.LeftSlotCoordinates shiftedReal.D shiftedReal.C
      (tensorObj W X) Y Z := ⟨qInner, l, outer⟩
  let c₂ : RealAssociatorLaws.LeftSlotCoordinates shiftedReal.D shiftedReal.C
      (tensorObj W X) Y Z :=
    ⟨⟨RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C W X
        (binarySlot W X i j ab), k,
      Associator.castIndex shiftedReal
        (binarySlot_position_label W X i j ab).symm rfl abc⟩,
      l,
      Associator.castIndex shiftedReal
        (congrArg (fun x => x + (Y.atom k).label)
          (binarySlot_position_label W X i j ab)).symm rfl abcd⟩
  have hc : c₁ = c₂ := by
    rfl
  calc
    _ = RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
        (tensorObj W X) Y Z c₁ := rfl
    _ = RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
        (tensorObj W X) Y Z c₂ := congrArg _ hc
    _ = _ := RealAssociatorLaws.leftSlotPack_route
      (tensorObj W X) Y Z _ _ _ _ _

private theorem quadRightSlot_as_outerRightRoute (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (abcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      Y Z (binarySlot Y Z k l cd)
    let hCD := binarySlot_position_label Y Z k l cd
    let bcd' := Associator.castIndex shiftedReal rfl hCD.symm bcd
    let hRest :
        (X.atom j).label + (Y.atom k).label + (Z.atom l).label =
          (X.atom j).label + ((tensorObj Y Z).atom pCD).label :=
      (_root_.add_assoc (X.atom j).label (Y.atom k).label
        (Z.atom l).label).trans
          (congrArg (fun x => (X.atom j).label + x) hCD.symm)
    let abcd' := Associator.castIndex shiftedReal rfl hRest abcd
    quadRightSlot W X Y Z i j k l cd bcd abcd =
      RealAssociatorLaws.rightRouteSlot W X (tensorObj Y Z)
        i j pCD bcd' abcd' := by
  dsimp only
  let qInner := RealAssociatorLaws.rightRouteSlot X Y Z j k l cd bcd
  let outer := Associator.castIndex shiftedReal rfl
    ((_root_.add_assoc (X.atom j).label (Y.atom k).label
      (Z.atom l).label).trans
        (RealAssociatorLaws.rightRouteSlot_label X Y Z
          j k l cd bcd).symm) abcd
  let c₁ : RealAssociatorLaws.RightSlotCoordinates shiftedReal.D shiftedReal.C
      W X (tensorObj Y Z) := ⟨i, qInner, outer⟩
  let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    Y Z (binarySlot Y Z k l cd)
  let hCD := binarySlot_position_label Y Z k l cd
  let hRest :
      (X.atom j).label + (Y.atom k).label + (Z.atom l).label =
        (X.atom j).label + ((tensorObj Y Z).atom pCD).label :=
    (_root_.add_assoc (X.atom j).label (Y.atom k).label
      (Z.atom l).label).trans
        (congrArg (fun x => (X.atom j).label + x) hCD.symm)
  let c₂ : RealAssociatorLaws.RightSlotCoordinates shiftedReal.D shiftedReal.C
      W X (tensorObj Y Z) :=
    ⟨i,
      ⟨j, pCD,
        Associator.castIndex shiftedReal rfl hCD.symm bcd⟩,
      Associator.castIndex shiftedReal rfl hRest abcd⟩
  have hc : c₁ = c₂ := by
    rfl
  calc
    _ = RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W X (tensorObj Y Z) c₁ := rfl
    _ = RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W X (tensorObj Y Z) c₂ := congrArg _ hc
    _ = _ := RealAssociatorLaws.rightSlotPack_route
      W X (tensorObj Y Z) _ _ _ _ _

private theorem bottomMiddleSlot_as_outerRightRoute (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      W X (binarySlot W X i j ab)
    let hAB := binarySlot_position_label W X i j ab
    let row' := Associator.castIndex shiftedReal hAB.symm rfl rowABCD
    bottomMiddleSlot W X Y Z i j k l ab cd rowABCD =
      RealAssociatorLaws.rightRouteSlot (tensorObj W X) Y Z
        pAB k l cd row' := by
  dsimp only
  let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    W X (binarySlot W X i j ab)
  let hAB := binarySlot_position_label W X i j ab
  let hCD := binarySlot_position_label Y Z k l cd
  let row' := Associator.castIndex shiftedReal hAB.symm rfl rowABCD
  let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
  let qR := RealAssociatorLaws.rightRouteSlot (tensorObj W X) Y Z
    pAB k l cd row'
  let hYZ := RealAssociatorLaws.rightRouteSlot_innerLabel
    (tensorObj W X) Y Z pAB k l cd row'
  have hmiddle : qM.fusion = Associator.castIndex shiftedReal
      hAB.symm hCD.symm rowABCD := by
    rfl
  have houter : Associator.castIndex shiftedReal rfl hYZ qR.fusion =
      row' := by
    simpa only [qR, hYZ] using
      (RealAssociatorLaws.rightRouteSlot_outerRow
        (tensorObj W X) Y Z pAB k l cd row')
  change qM = qR
  have hleft : qM.left = qR.left := by
    simp only [qM, qR, bottomMiddleSlot_left,
      RealAssociatorLaws.rightRouteSlot_left]
    rfl
  have hright : qM.right = qR.right := by
    apply (RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
      Y Z).injective
    rw [RealAssociatorLaws.slotsEquiv_apply,
      RealAssociatorLaws.slotsEquiv_apply]
    rw [show (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qM.right =
        binarySlot Y Z k l cd by
      simp only [qM, bottomMiddleSlot_right,
        RealAssociatorLaws.get_slotPosition]]
    simpa only [qR, binarySlot] using
      (RealAssociatorLaws.rightRouteSlot_inner
        (tensorObj W X) Y Z pAB k l cd row').symm
  apply Sigma.ext hleft
  cases hleft
  apply heq_of_eq
  apply Sigma.ext hright
  cases hright
  apply heq_of_eq
  apply castIndex_injective rfl hYZ
  calc
    _ = Associator.castIndex shiftedReal rfl hYZ
        (Associator.castIndex shiftedReal hAB.symm hCD.symm rowABCD) :=
      congrArg (Associator.castIndex shiftedReal rfl hYZ) hmiddle
    _ = row' := by
      rw [castIndex_trans]
    _ = _ := houter.symm

private theorem bottomMiddleSlot_as_outerLeftRoute (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      Y Z (binarySlot Y Z k l cd)
    let hCD := binarySlot_position_label Y Z k l cd
    let row' := Associator.castIndex shiftedReal rfl hCD.symm rowABCD
    bottomMiddleSlot W X Y Z i j k l ab cd rowABCD =
      RealAssociatorLaws.leftRouteSlot W X (tensorObj Y Z)
        i j pCD ab row' := by
  dsimp only
  let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    Y Z (binarySlot Y Z k l cd)
  let hAB := binarySlot_position_label W X i j ab
  let hCD := binarySlot_position_label Y Z k l cd
  let row' := Associator.castIndex shiftedReal rfl hCD.symm rowABCD
  let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
  let qL := RealAssociatorLaws.leftRouteSlot W X (tensorObj Y Z)
    i j pCD ab row'
  let hWX := RealAssociatorLaws.leftRouteSlot_innerLabel
    W X (tensorObj Y Z) i j pCD ab row'
  have hmiddle : qM.fusion = Associator.castIndex shiftedReal
      hAB.symm hCD.symm rowABCD := by
    rfl
  have houter : Associator.castIndex shiftedReal hWX rfl qL.fusion =
      row' := by
    simpa only [qL, hWX] using
      (RealAssociatorLaws.leftRouteSlot_outerRow
        W X (tensorObj Y Z) i j pCD ab row')
  change qM = qL
  have hleft : qM.left = qL.left := by
    apply (RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
      W X).injective
    rw [RealAssociatorLaws.slotsEquiv_apply,
      RealAssociatorLaws.slotsEquiv_apply]
    rw [show (Tensor.slots shiftedReal.D shiftedReal.C W X).get qM.left =
        binarySlot W X i j ab by
      simp only [qM, bottomMiddleSlot_left,
        RealAssociatorLaws.get_slotPosition]]
    simpa only [qL, binarySlot] using
      (RealAssociatorLaws.leftRouteSlot_inner
        W X (tensorObj Y Z) i j pCD ab row').symm
  have hright : qM.right = qL.right := by
    simp only [qM, qL, bottomMiddleSlot_right,
      RealAssociatorLaws.leftRouteSlot_right]
    rfl
  apply Sigma.ext hleft
  cases hleft
  apply heq_of_eq
  apply Sigma.ext hright
  cases hright
  apply heq_of_eq
  apply castIndex_injective hWX rfl
  calc
    _ = Associator.castIndex shiftedReal hWX rfl
        (Associator.castIndex shiftedReal hAB.symm hCD.symm rowABCD) :=
      congrArg (Associator.castIndex shiftedReal hWX rfl) hmiddle
    _ = row' := by
      rw [castIndex_trans]
    _ = _ := houter.symm

/-- The first bottom associator entry, transported to the four-object total,
is the normalized shifted connector for the labels `(a + b, c, d)`. -/
private theorem cast_bottomFirstHomEntry_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
    let hM := bottomMiddleSlot_label W X Y Z i j k l ab cd rowABCD
    cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hS)
        ((RealAssociator.homEntry (tensorObj W X) Y Z qS qM).coeff
          (hS.trans hM.symm)) =
      (shiftedReal.D.algebra t).smul
        (RawDCT.paritySign
          (shiftedReal.C.rowParity
            ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc *
              (Z.atom l).shift))
      (Associator.homCoefficient shiftedReal
          ((W.atom i).label + (X.atom j).label) (Y.atom k).label
          (Z.atom l).label abc sourceABCD cd rowABCD) := by
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
  let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
  let hM := bottomMiddleSlot_label W X Y Z i j k l ab cd rowABCD
  let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    W X (binarySlot W X i j ab)
  let hAB := binarySlot_position_label W X i j ab
  let abc' := Associator.castIndex shiftedReal hAB.symm rfl abc
  let sourceABCD' := Associator.castIndex shiftedReal
    (congrArg (fun a => a + (Y.atom k).label) hAB).symm rfl sourceABCD
  let rowABCD' := Associator.castIndex shiftedReal hAB.symm rfl rowABCD
  let qL := RealAssociatorLaws.leftRouteSlot (tensorObj W X) Y Z
    pAB k l abc' sourceABCD'
  let qR := RealAssociatorLaws.rightRouteSlot (tensorObj W X) Y Z
    pAB k l cd rowABCD'
  have hqS : qS = qL := quadLeftSlot_as_outerLeftRoute W X Y Z
    i j k l ab abc sourceABCD
  have hqM : qM = qR := bottomMiddleSlot_as_outerRightRoute W X Y Z
    i j k l ab cd rowABCD
  let hTotal : ((tensorObj W X).atom pAB).label + (Y.atom k).label +
      (Z.atom l).label =
        t :=
    congrArg (fun a => a + (Y.atom k).label + (Z.atom l).label) hAB
  let hL := RealAssociatorLaws.leftRouteSlot_label
    (tensorObj W X) Y Z pAB k l abc' sourceABCD'
  let hR := RealAssociatorLaws.rightRouteSlot_label
    (tensorObj W X) Y Z pAB k l cd rowABCD'
  let hLT : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z qL).label = t :=
    hL.trans hTotal
  let hRT : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z) qR).label = t :=
    hR.trans ((_root_.add_assoc ((tensorObj W X).atom pAB).label
      (Y.atom k).label (Z.atom l).label).symm.trans hTotal)
  have hSlots := cast_homEntry_coeff_of_slots_eq
    (tensorObj W X) Y Z qS qL qM qR hqS hqM t hS hM hLT hRT
  have h := cast_normalizedHomEntry_route_coeff
    (tensorObj W X) Y Z pAB k l abc' sourceABCD' cd rowABCD'
      t hTotal
  rw [hSlots]
  rw [h]
  rw [cast_smul]
  have hParity : shiftedReal.C.rowParity
      ((tensorObj W X).atom pAB).label (Y.atom k).label abc' =
        shiftedReal.C.rowParity
          ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc := by
    simpa only [abc'] using rowParity_castIndex hAB.symm rfl abc
  rw [hParity]
  have hCoeff := cast_homCoefficient_first_label hAB
    abc sourceABCD cd rowABCD
  rw [hCoeff]
  exact hTotal

/-- The second bottom associator entry is the normalized shifted connector
for `(a,b,c+d)`.  Its natural total is `(a+b)+(c+d)`, so the final
associativity transport to the fixed four-object total remains explicit. -/
private theorem cast_bottomSecondHomEntry_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (rowABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label)
      ((Y.atom k).label + (Z.atom l).label)) :
    let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let hM := bottomMiddleSlot_label W X Y Z i j k l ab cd rowABCD
    let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) qT).label = t :=
      (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
        ((_root_.add_assoc (W.atom i).label (X.atom j).label
          ((Y.atom k).label + (Z.atom l).label)).symm.trans
         (_root_.add_assoc ((W.atom i).label + (X.atom j).label)
          (Y.atom k).label (Z.atom l).label).symm)
    cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hM)
        ((RealAssociator.homEntry W X (tensorObj Y Z) qM qT).coeff
          (hM.trans hT.symm)) =
      let hAssoc := (_root_.add_assoc
        ((W.atom i).label + (X.atom j).label)
        (Y.atom k).label (Z.atom l).label).symm
      cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hAssoc)
        ((shiftedReal.D.algebra
          (((W.atom i).label + (X.atom j).label) +
            ((Y.atom k).label + (Z.atom l).label))).smul
          (RawDCT.paritySign
            (shiftedReal.C.rowParity
                (W.atom i).label (X.atom j).label ab *
              ((Y.atom k).shift + (Z.atom l).shift +
                shiftedReal.C.rowParity
                  (Y.atom k).label (Z.atom l).label cd)))
          (Associator.homCoefficient shiftedReal
            (W.atom i).label (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label)
            ab rowABCD bcd
            (Associator.castIndex shiftedReal rfl
              (_root_.add_assoc (X.atom j).label
                (Y.atom k).label (Z.atom l).label)
              targetABCD))) := by
  dsimp only
  let qM := bottomMiddleSlot W X Y Z i j k l ab cd rowABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let hM := bottomMiddleSlot_label W X Y Z i j k l ab cd rowABCD
  let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) qT).label = t :=
    (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
      ((_root_.add_assoc (W.atom i).label (X.atom j).label
        ((Y.atom k).label + (Z.atom l).label)).symm.trans
       (_root_.add_assoc ((W.atom i).label + (X.atom j).label)
        (Y.atom k).label (Z.atom l).label).symm)
  let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    Y Z (binarySlot Y Z k l cd)
  let hCD := binarySlot_position_label Y Z k l cd
  let rowABCD' := Associator.castIndex shiftedReal rfl hCD.symm rowABCD
  let bcd' := Associator.castIndex shiftedReal rfl hCD.symm bcd
  let hRest := (_root_.add_assoc (X.atom j).label (Y.atom k).label
    (Z.atom l).label).trans
      (congrArg (fun q => (X.atom j).label + q) hCD.symm)
  let targetABCD' := Associator.castIndex shiftedReal rfl hRest targetABCD
  let qL := RealAssociatorLaws.leftRouteSlot W X (tensorObj Y Z)
    i j pCD ab rowABCD'
  let qR := RealAssociatorLaws.rightRouteSlot W X (tensorObj Y Z)
    i j pCD bcd' targetABCD'
  have hqM : qM = qL := bottomMiddleSlot_as_outerLeftRoute
    W X Y Z i j k l ab cd rowABCD
  have hqT : qT = qR := quadRightSlot_as_outerRightRoute
    W X Y Z i j k l cd bcd targetABCD
  let hAssoc := (_root_.add_assoc
    ((W.atom i).label + (X.atom j).label)
    (Y.atom k).label (Z.atom l).label).symm
  let hCDTotal := congrArg
    (fun q => (W.atom i).label + (X.atom j).label + q) hCD
  let hTotal : (W.atom i).label + (X.atom j).label +
      ((tensorObj Y Z).atom pCD).label = t :=
    hCDTotal.trans hAssoc
  let hL := RealAssociatorLaws.leftRouteSlot_label
    W X (tensorObj Y Z) i j pCD ab rowABCD'
  let hR := RealAssociatorLaws.rightRouteSlot_label
    W X (tensorObj Y Z) i j pCD bcd' targetABCD'
  let hLT : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z) qL).label = t :=
    hL.trans hTotal
  let hRT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) qR).label = t :=
    hR.trans ((_root_.add_assoc (W.atom i).label (X.atom j).label
      ((tensorObj Y Z).atom pCD).label).symm.trans hTotal)
  have hSlots := cast_homEntry_coeff_of_slots_eq
    W X (tensorObj Y Z) qM qL qT qR hqM hqT t hM hT hLT hRT
  have h := cast_normalizedHomEntry_route_coeff
    W X (tensorObj Y Z) i j pCD ab rowABCD' bcd' targetABCD'
      t hTotal
  rw [hSlots]
  rw [h]
  rw [cast_smul shiftedReal.D hTotal]
  rw [cast_smul shiftedReal.D hAssoc]
  have hShift : ((tensorObj Y Z).atom pCD).shift =
      (Y.atom k).shift + (Z.atom l).shift +
        shiftedReal.C.rowParity
          (Y.atom k).label (Z.atom l).label cd := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z
      ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get pCD)).shift = _
    rw [RealAssociatorLaws.get_slotPosition]
    rfl
  rw [hShift]
  let targetCanonical := Associator.castIndex shiftedReal rfl
    (_root_.add_assoc (X.atom j).label (Y.atom k).label (Z.atom l).label)
    targetABCD
  have hTargetTransport : targetABCD' =
      Associator.castIndex shiftedReal rfl
        (congrArg (fun q => (X.atom j).label + q) hCD).symm
        targetCanonical := by
    dsimp only [targetABCD', targetCanonical]
    rw [castIndex_trans]
  have hThird := cast_homCoefficient_third_label hCD
    ab rowABCD bcd targetCanonical
  rw [← hTargetTransport] at hThird
  have hCastSplit
      (u : (shiftedReal.D.algebra
        ((W.atom i).label + (X.atom j).label +
          ((tensorObj Y Z).atom pCD).label)).carrier) :
      cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hTotal) u =
        cast (congrArg
            (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hAssoc)
          (cast (congrArg
              (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier)
              hCDTotal) u) := by
    rw [show hTotal = hCDTotal.trans hAssoc by apply Subsingleton.elim]
    exact (cast_cast_route
      (congrArg (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier)
        hCDTotal)
      (congrArg (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier)
        hAssoc) u).symm
  rw [hCastSplit]
  rw [hThird]

/-! ### Canonical middle slots on the three-edge route

The following two constructors are the finite-coordinate counterparts of
the two intermediate vertices of the already existing semantic top route.
They only repackage object positions and fusion rows; no connector entry or
fourfold table is evaluated here.
-/

/-- Slot after the first, right-whiskered associator. -/
private def topFirstMiddleSlot (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z := by
  let qInner := RealAssociatorLaws.rightRouteSlot W X Y i j k bc a_bc
  let hInner := RealAssociatorLaws.rightRouteSlot_label
    W X Y i j k bc a_bc
  exact RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
    W (tensorObj X Y) Z
      ⟨qInner, l,
        Associator.castIndex shiftedReal
          ((_root_.add_assoc (W.atom i).label (X.atom j).label
            (Y.atom k).label).trans hInner.symm) rfl rowLast⟩

/-- Slot after the middle associator and before the final left whisker. -/
private def topSecondMiddleSlot (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj (tensorObj X Y) Z) := by
  let qInner := RealAssociatorLaws.leftRouteSlot X Y Z j k l bc bc_d
  let hInner := RealAssociatorLaws.leftRouteSlot_label
    X Y Z j k l bc bc_d
  exact RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
    W (tensorObj X Y) Z
      ⟨i, qInner,
        Associator.castIndex shiftedReal rfl hInner.symm a_bcd⟩

/-- The first intermediate top slot is the canonical left-route slot for
the outer connector on `(W, X ⊗ Y, Z)`. -/
private theorem topFirstMiddleSlot_as_outerLeftRoute (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      X Y (binarySlot X Y j k bc)
    let hBC := binarySlot_position_label X Y j k bc
    let a_bc' := Associator.castIndex shiftedReal rfl hBC.symm a_bc
    let hABC :
        (W.atom i).label + (X.atom j).label + (Y.atom k).label =
          (W.atom i).label + ((tensorObj X Y).atom pBC).label :=
      (_root_.add_assoc (W.atom i).label (X.atom j).label
        (Y.atom k).label).trans
          (congrArg (fun q => (W.atom i).label + q) hBC.symm)
    let rowLast' := Associator.castIndex shiftedReal hABC rfl rowLast
    topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast =
      RealAssociatorLaws.leftRouteSlot W (tensorObj X Y) Z
        i pBC l a_bc' rowLast' := by
  dsimp only
  let qInner := RealAssociatorLaws.rightRouteSlot W X Y
    i j k bc a_bc
  let hInner := RealAssociatorLaws.rightRouteSlot_label W X Y
    i j k bc a_bc
  let outer := Associator.castIndex shiftedReal
    ((_root_.add_assoc (W.atom i).label (X.atom j).label
      (Y.atom k).label).trans hInner.symm) rfl rowLast
  let c₁ : RealAssociatorLaws.LeftSlotCoordinates
      shiftedReal.D shiftedReal.C W (tensorObj X Y) Z :=
    ⟨qInner, l, outer⟩
  let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    X Y (binarySlot X Y j k bc)
  let hBC := binarySlot_position_label X Y j k bc
  let a_bc' := Associator.castIndex shiftedReal rfl hBC.symm a_bc
  let hABC :
      (W.atom i).label + (X.atom j).label + (Y.atom k).label =
        (W.atom i).label + ((tensorObj X Y).atom pBC).label :=
    (_root_.add_assoc (W.atom i).label (X.atom j).label
      (Y.atom k).label).trans
        (congrArg (fun q => (W.atom i).label + q) hBC.symm)
  let rowLast' := Associator.castIndex shiftedReal hABC rfl rowLast
  let c₂ : RealAssociatorLaws.LeftSlotCoordinates
      shiftedReal.D shiftedReal.C W (tensorObj X Y) Z :=
    ⟨⟨i, pBC, a_bc'⟩, l, rowLast'⟩
  have hc : c₁ = c₂ := by
    rfl
  calc
    _ = RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z c₁ := rfl
    _ = RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z c₂ := congrArg _ hc
    _ = _ := RealAssociatorLaws.leftSlotPack_route
      W (tensorObj X Y) Z i pBC l a_bc' rowLast'

/-- The second intermediate top slot is the canonical right-route slot for
the same outer connector. -/
private theorem topSecondMiddleSlot_as_outerRightRoute (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
      X Y (binarySlot X Y j k bc)
    let hBC := binarySlot_position_label X Y j k bc
    let bc_d' := Associator.castIndex shiftedReal hBC.symm rfl bc_d
    let hBCD :
        (X.atom j).label + (Y.atom k).label + (Z.atom l).label =
          ((tensorObj X Y).atom pBC).label + (Z.atom l).label :=
      congrArg (fun q => q + (Z.atom l).label) hBC.symm
    let a_bcd' := Associator.castIndex shiftedReal rfl hBCD a_bcd
    topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd =
      RealAssociatorLaws.rightRouteSlot W (tensorObj X Y) Z
        i pBC l bc_d' a_bcd' := by
  dsimp only
  let qInner := RealAssociatorLaws.leftRouteSlot X Y Z
    j k l bc bc_d
  let hInner := RealAssociatorLaws.leftRouteSlot_label X Y Z
    j k l bc bc_d
  let outer := Associator.castIndex shiftedReal rfl hInner.symm a_bcd
  let c₁ : RealAssociatorLaws.RightSlotCoordinates
      shiftedReal.D shiftedReal.C W (tensorObj X Y) Z :=
    ⟨i, qInner, outer⟩
  let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    X Y (binarySlot X Y j k bc)
  let hBC := binarySlot_position_label X Y j k bc
  let bc_d' := Associator.castIndex shiftedReal hBC.symm rfl bc_d
  let hBCD :
      (X.atom j).label + (Y.atom k).label + (Z.atom l).label =
        ((tensorObj X Y).atom pBC).label + (Z.atom l).label :=
    congrArg (fun q => q + (Z.atom l).label) hBC.symm
  let a_bcd' := Associator.castIndex shiftedReal rfl hBCD a_bcd
  let c₂ : RealAssociatorLaws.RightSlotCoordinates
      shiftedReal.D shiftedReal.C W (tensorObj X Y) Z :=
    ⟨i, ⟨pBC, l, bc_d'⟩, a_bcd'⟩
  have hc : c₁ = c₂ := by
    rfl
  calc
    _ = RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z c₁ := rfl
    _ = RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z c₂ := congrArg _ hc
    _ = _ := RealAssociatorLaws.rightSlotPack_route
      W (tensorObj X Y) Z i pBC l bc_d' a_bcd'

@[simp] private theorem topFirstMiddleSlot_inner (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    (Tensor.slots shiftedReal.D shiftedReal.C W (tensorObj X Y)).get
        (topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast).left =
      RealAssociatorLaws.rightRouteSlot W X Y i j k bc a_bc := by
  unfold topFirstMiddleSlot
  apply RealAssociatorLaws.leftSlotPack_inner

@[simp] private theorem topFirstMiddleSlot_right (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    (topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast).right = l := by
  unfold topFirstMiddleSlot
  apply RealAssociatorLaws.leftSlotPack_right

@[simp] private theorem topSecondMiddleSlot_left (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd).left = i := by
  unfold topSecondMiddleSlot
  apply RealAssociatorLaws.rightSlotPack_left

@[simp] private theorem topSecondMiddleSlot_inner (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (Tensor.slots shiftedReal.D shiftedReal.C (tensorObj X Y) Z).get
        (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd).right =
      RealAssociatorLaws.leftRouteSlot X Y Z j k l bc bc_d := by
  unfold topSecondMiddleSlot
  apply RealAssociatorLaws.rightSlotPack_inner

private theorem topFirstMiddleSlot_label (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z
      (topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast)).label =
        (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C W (tensorObj X Y)
      ((Tensor.slots shiftedReal.D shiftedReal.C W (tensorObj X Y)).get
        (topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast).left)).label +
    (Z.atom (topFirstMiddleSlot W X Y Z
      i j k l bc a_bc rowLast).right).label = _
  rw [topFirstMiddleSlot_inner, topFirstMiddleSlot_right,
    RealAssociatorLaws.rightRouteSlot_label]
  ac_rfl

private theorem topSecondMiddleSlot_label (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj (tensorObj X Y) Z)
      (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd)).label =
        (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label := by
  change (W.atom (topSecondMiddleSlot W X Y Z
      i j k l bc bc_d a_bcd).left).label +
    (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj X Y) Z
      ((Tensor.slots shiftedReal.D shiftedReal.C (tensorObj X Y) Z).get
        (topSecondMiddleSlot W X Y Z
          i j k l bc bc_d a_bcd).right)).label = _
  rw [topSecondMiddleSlot_left, topSecondMiddleSlot_inner,
    RealAssociatorLaws.leftRouteSlot_label]
  ac_rfl

/-! ### Lowering the three supported top-route edges

Each bridge below only transports a supported semantic matrix entry to the
already stored ternary connector coefficient.  In particular, none of them
evaluates the four-object pentagon table. -/

/-- The first, right-whiskered associator entry is its stored ternary
coefficient acted on by the outer binary fusion row. -/
private theorem cast_topFirstTensorEntry_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let q₁ := topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
    let h₁ := topFirstMiddleSlot_label W X Y Z
      i j k l bc a_bc rowLast
    let P₁ := rawReal.T.parity
        (W.atom i).label (X.atom j).label (Y.atom k).label +
      rawRowParityOfShifted (W.atom i).label (X.atom j).label ab +
      rawRowParityOfShifted
        ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc +
      rawRowParityOfShifted (X.atom j).label (Y.atom k).label bc +
      rawRowParityOfShifted (W.atom i).label
        ((X.atom j).label + (Y.atom k).label) a_bc
    cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hS)
        ((Tensor.entry shiftedReal.D shiftedReal.C
          (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁).coeff
            (hS.trans h₁.symm)) =
      (shiftedReal.D.algebra t).smul
        (RawDCT.paritySign
          (((Z.atom l).shift +
              shiftNu realComputableNuBeta.data
                ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
                (Z.atom l).label) * P₁))
        ((shiftedReal.D.algebra t).smul
          (RawDCT.paritySign
            (shiftedReal.C.rowParity
                (W.atom i).label (X.atom j).label ab *
              (Y.atom k).shift))
          (rawReal.C.leftCoeff
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
            (Z.atom l).label rowLast sourceABCD
            (Associator.homCoefficient shiftedReal
              (W.atom i).label (X.atom j).label (Y.atom k).label
              ab abc bc a_bc)
            (rawReal.D.algebra (Z.atom l).label).one)) := by
  dsimp only
  let qS : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z :=
    quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let q₁ : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z :=
    topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast
  let t : ZMod 8 :=
    (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let hS : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z qS).label = t :=
    quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
  let h₁ : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z q₁).label = t :=
    topFirstMiddleSlot_label W X Y Z i j k l bc a_bc rowLast
  let P₁ := rawReal.T.parity
        (W.atom i).label (X.atom j).label (Y.atom k).label +
      rawRowParityOfShifted (W.atom i).label (X.atom j).label ab +
      rawRowParityOfShifted
        ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc +
      rawRowParityOfShifted (X.atom j).label (Y.atom k).label bc +
      rawRowParityOfShifted (W.atom i).label
        ((X.atom j).label + (Y.atom k).label) a_bc
  let qL := RealAssociatorLaws.leftRouteSlot W X Y i j k ab abc
  let qR := RealAssociatorLaws.rightRouteSlot W X Y i j k bc a_bc
  have hGetS :
      (Tensor.slots shiftedReal.D shiftedReal.C (tensorObj W X) Y).get
          qS.left = qL := by
    simpa only [qS, qL] using
      (quadLeftSlot_inner W X Y Z i j k l ab abc sourceABCD)
  have hGet₁ :
      (Tensor.slots shiftedReal.D shiftedReal.C W (tensorObj X Y)).get
          q₁.left = qR := by
    simpa only [q₁, qR] using
      (topFirstMiddleSlot_inner W X Y Z i j k l bc a_bc rowLast)
  have hsRight : qS.right = l := by
    simpa only [qS] using
      (quadLeftSlot_right W X Y Z i j k l ab abc sourceABCD)
  have htRight : q₁.right = l := by
    simpa only [q₁] using
      (topFirstMiddleSlot_right W X Y Z i j k l bc a_bc rowLast)
  let hA : ((tensorObj (tensorObj W X) Y).atom qS.left).label =
      ((tensorObj W (tensorObj X Y)).atom q₁.left).label := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (tensorObj W X) Y
        ((Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj W X) Y).get qS.left)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C W (tensorObj X Y)
        ((Tensor.slots shiftedReal.D shiftedReal.C
          W (tensorObj X Y)).get q₁.left)).label
    rw [hGetS, hGet₁]
    exact RealAssociatorLaws.routeAssocLabelEq
      W X Y i j k ab abc bc a_bc
  let hB : (Z.atom qS.right).label = (Z.atom q₁.right).label :=
    congrArg (fun r => (Z.atom r).label) (hsRight.trans htRight.symm)
  let hLeft : ((tensorObj (tensorObj W X) Y).atom qS.left).label =
      (W.atom i).label + (X.atom j).label + (Y.atom k).label := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W X) Y
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (tensorObj W X) Y).get qS.left)).label = _
    rw [hGetS]
    exact RealAssociatorLaws.leftRouteSlot_label
      W X Y i j k ab abc
  let hRight : (Z.atom qS.right).label = (Z.atom l).label :=
    congrArg (fun r => (Z.atom r).label) hsRight
  let hLeftTotal :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (tensorObj (tensorObj W X) Y) Z qS).label =
        (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom qS.right).label :=
    congrArg (fun q => q + (Z.atom qS.right).label) hLeft
  let hRightTotal :
      (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom qS.right).label = t :=
    congrArg
      (fun q => (W.atom i).label + (X.atom j).label +
        (Y.atom k).label + q) hRight
  have hTotalProof : hS = hLeftTotal.trans hRightTotal :=
    Subsingleton.elim _ _
  have hCastSplit
      (u : (shiftedReal.D.algebra
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z qS).label).carrier) :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hS) u =
        cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
            hRightTotal)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              hLeftTotal) u) := by
    rw [hTotalProof]
    exact (cast_cast_route
      (congrArg (fun q : ZMod 8 =>
        (shiftedReal.D.algebra q).carrier) hLeftTotal)
      (congrArg (fun q : ZMod 8 =>
        (shiftedReal.D.algebra q).carrier) hRightTotal) u).symm
  have hEntry := tensorEntry_coeff_of_label_eq
    (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
    qS q₁ hA hB (hS.trans h₁.symm)
  have hEntryCast := congrArg
    (fun u => cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
        hRightTotal)
      (cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
          hLeftTotal) u))
    hEntry
  let xAssoc :=
    (shiftedReal.D.algebra
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)).smul
      (RawDCT.paritySign
        (shiftedReal.C.rowParity
            (W.atom i).label (X.atom j).label ab * (Y.atom k).shift))
      (Associator.homCoefficient shiftedReal
        (W.atom i).label (X.atom j).label (Y.atom k).label
        ab abc bc a_bc)
  have hAssocInput :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
        (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA) =
      xAssoc := by
    change cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
      ((RealAssociator.homEntry W X Y
        ((Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj W X) Y).get qS.left)
        ((Tensor.slots shiftedReal.D shiftedReal.C
          W (tensorObj X Y)).get q₁.left)).coeff hA) = xAssoc
    let A := (W.atom i).label + (X.atom j).label + (Y.atom k).label
    let hTarget :
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W (tensorObj X Y)
          ((Tensor.slots shiftedReal.D shiftedReal.C
            W (tensorObj X Y)).get q₁.left)).label = A :=
      hA.symm.trans hLeft
    let hL := RealAssociatorLaws.leftRouteSlot_label
      W X Y i j k ab abc
    let hR := (RealAssociatorLaws.rightRouteSlot_label
      W X Y i j k bc a_bc).trans
        (_root_.add_assoc (W.atom i).label (X.atom j).label
          (Y.atom k).label).symm
    have hp : hA = hLeft.trans hTarget.symm := Subsingleton.elim _ _
    rw [hp]
    have hSlots := cast_homEntry_coeff_of_slots_eq W X Y
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (tensorObj W X) Y).get qS.left) qL
      ((Tensor.slots shiftedReal.D shiftedReal.C
        W (tensorObj X Y)).get q₁.left) qR
      hGetS hGet₁ A hLeft hTarget hL hR
    have hRoute := RealAssociatorNaturality.realHomEntry_route_coeff
      W X Y i j k ab abc bc a_bc
    have hRouteNormalized :
        cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hL)
          ((RealAssociator.homEntry W X Y qL qR).coeff
            (hL.trans hR.symm)) = xAssoc := by
      rw [show hL.trans hR.symm =
          RealAssociatorLaws.routeAssocLabelEq
            W X Y i j k ab abc bc a_bc by
        apply Subsingleton.elim]
      dsimp only [qL, qR]
      rw [hRoute]
      exact cast_algebra_symm_cancel shiftedReal.D hL xAssoc
    exact hSlots.trans hRouteNormalized
  let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    W X (binarySlot W X i j ab)
  let hAB := binarySlot_position_label W X i j ab
  let abcOuter := Associator.castIndex shiftedReal hAB.symm rfl abc
  let sourceOuter := Associator.castIndex shiftedReal
    (congrArg (fun q => q + (Y.atom k).label) hAB).symm rfl sourceABCD
  let qSOuter := RealAssociatorLaws.leftRouteSlot
    (tensorObj W X) Y Z pAB k l abcOuter sourceOuter
  have hqSOuter : qS = qSOuter :=
    quadLeftSlot_as_outerLeftRoute W X Y Z
      i j k l ab abc sourceABCD
  have hSource :
      Associator.castIndex shiftedReal rfl hRight
        (Associator.castIndex shiftedReal hLeft rfl qS.fusion) =
      sourceABCD := by
    apply Fin.ext
    simp only [castIndex_val]
    rw [hqSOuter]
    have hv := congrArg Fin.val
      (RealAssociatorLaws.leftRouteSlot_outerRow
        (tensorObj W X) Y Z pAB k l abcOuter sourceOuter)
    simpa only [qSOuter, sourceOuter, castIndex_val] using hv
  let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    X Y (binarySlot X Y j k bc)
  let hBC := binarySlot_position_label X Y j k bc
  let a_bcOuter := Associator.castIndex shiftedReal rfl hBC.symm a_bc
  let hABC :
      (W.atom i).label + (X.atom j).label + (Y.atom k).label =
        (W.atom i).label + ((tensorObj X Y).atom pBC).label :=
    (_root_.add_assoc (W.atom i).label (X.atom j).label
      (Y.atom k).label).trans
        (congrArg (fun q => (W.atom i).label + q) hBC.symm)
  let rowLastOuter := Associator.castIndex shiftedReal hABC rfl rowLast
  let q₁Outer := RealAssociatorLaws.leftRouteSlot
    W (tensorObj X Y) Z i pBC l a_bcOuter rowLastOuter
  have hq₁Outer : q₁ = q₁Outer :=
    topFirstMiddleSlot_as_outerLeftRoute W X Y Z
      i j k l bc a_bc rowLast
  have hTarget :
      Associator.castIndex shiftedReal rfl hRight
        (Associator.castIndex shiftedReal hLeft rfl
          (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion)) =
      rowLast := by
    apply Fin.ext
    simp only [castIndex_val]
    rw [hq₁Outer]
    have hv := congrArg Fin.val
      (RealAssociatorLaws.leftRouteSlot_outerRow
        W (tensorObj X Y) Z i pBC l a_bcOuter rowLastOuter)
    simpa only [q₁Outer, rowLastOuter, castIndex_val] using hv
  have hId :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRight)
        (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB) =
      (shiftedReal.D.algebra (Z.atom l).label).one := by
    exact cast_homId_coeff shiftedReal.D Z qS.right q₁.right
      (hsRight.trans htRight.symm) hB (Z.atom l).label hRight
  let sOuter := ((tensorObj (tensorObj W X) Y).atom qS.left).shift
  let A := (W.atom i).label + (X.atom j).label + (Y.atom k).label
  have hLeftCoefficient := tensorCoefficient_cast_left_label
    ((tensorObj (tensorObj W X) Y).atom qS.left).label A
    (Z.atom qS.right).label hLeft sOuter
    (Z.atom qS.right).shift (Z.atom q₁.right).shift
    qS.fusion (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion)
    (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA)
    (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)
  have hLeftTransport :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
          hLeftTotal)
        (Tensor.coefficient shiftedReal.D shiftedReal.C
          ((tensorObj (tensorObj W X) Y).atom qS.left).label
          (Z.atom qS.right).label sOuter
          (Z.atom qS.right).shift (Z.atom q₁.right).shift
          qS.fusion
          (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion)
          (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA)
          (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)) =
        Tensor.coefficient shiftedReal.D shiftedReal.C
          A (Z.atom qS.right).label sOuter
          (Z.atom qS.right).shift (Z.atom q₁.right).shift
          (Associator.castIndex shiftedReal hLeft rfl qS.fusion)
          (Associator.castIndex shiftedReal hLeft rfl
            (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
            (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA))
          (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB) := by
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
            (congrArg (fun q => q + (Z.atom qS.right).label) hLeft))
          (Tensor.coefficient shiftedReal.D shiftedReal.C
            ((tensorObj (tensorObj W X) Y).atom qS.left).label
            (Z.atom qS.right).label sOuter
            (Z.atom qS.right).shift (Z.atom q₁.right).shift
            qS.fusion
            (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion)
            (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA)
            (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)) :=
        cast_proof_irrel _ _ _
      _ = _ := hLeftCoefficient
  have hEntryLeft := hEntryCast.trans
    (congrArg
      (fun u => cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
        hRightTotal) u)
      hLeftTransport)
  have hRightCoefficient := tensorCoefficient_cast_right_label
    A (Z.atom qS.right).label (Z.atom l).label hRight sOuter
    (Z.atom qS.right).shift (Z.atom q₁.right).shift
    (Associator.castIndex shiftedReal hLeft rfl qS.fusion)
    (Associator.castIndex shiftedReal hLeft rfl
      (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion))
    (cast (congrArg
      (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
      (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA))
    (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)
  have hRightTransport :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
          hRightTotal)
        (Tensor.coefficient shiftedReal.D shiftedReal.C
          A (Z.atom qS.right).label sOuter
          (Z.atom qS.right).shift (Z.atom q₁.right).shift
          (Associator.castIndex shiftedReal hLeft rfl qS.fusion)
          (Associator.castIndex shiftedReal hLeft rfl
            (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
            (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA))
          (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)) =
        Tensor.coefficient shiftedReal.D shiftedReal.C
          A (Z.atom l).label sOuter
          (Z.atom qS.right).shift (Z.atom q₁.right).shift
          (Associator.castIndex shiftedReal rfl hRight
            (Associator.castIndex shiftedReal hLeft rfl qS.fusion))
          (Associator.castIndex shiftedReal rfl hRight
            (Associator.castIndex shiftedReal hLeft rfl
              (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion)))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
            (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRight)
            (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)) := by
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
            (congrArg (fun q => A + q) hRight))
          (Tensor.coefficient shiftedReal.D shiftedReal.C
            A (Z.atom qS.right).label sOuter
            (Z.atom qS.right).shift (Z.atom q₁.right).shift
            (Associator.castIndex shiftedReal hLeft rfl qS.fusion)
            (Associator.castIndex shiftedReal hLeft rfl
              (Associator.castIndex shiftedReal hA.symm hB.symm q₁.fusion))
            (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
              (((RealAssociator.hom W X Y) qS.left q₁.left).coeff hA))
            (((Hom.id shiftedReal.D Z) qS.right q₁.right).coeff hB)) :=
        cast_proof_irrel _ _ _
      _ = _ := hRightCoefficient
  have hEntryRight := hEntryLeft.trans hRightTransport
  rw [hSource, hTarget, hAssocInput, hId] at hEntryRight
  have hLowered :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hS)
        ((Tensor.entry shiftedReal.D shiftedReal.C
          (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁).coeff
            (hS.trans h₁.symm)) =
      Tensor.coefficient shiftedReal.D shiftedReal.C
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
        (Z.atom l).label sOuter (Z.atom l).shift (Z.atom l).shift
        sourceABCD rowLast xAssoc
        (shiftedReal.D.algebra (Z.atom l).label).one := by
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
            hRightTotal)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              hLeftTotal)
            ((Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
              qS q₁).coeff (hS.trans h₁.symm))) := hCastSplit _
      _ = _ := by
        simpa only [A, sOuter, hsRight, htRight] using hEntryRight
  have hx := realShiftedHomCoefficient_memGrade_raw
    (W.atom i).label (X.atom j).label (Y.atom k).label
    ab abc bc a_bc
  have hxNorm :
      (shiftedReal.D.algebra
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label)).MemGrade
        P₁ xAssoc := by
    dsimp only [xAssoc]
    unfold SuperAlgebraData.MemGrade at hx ⊢
    rw [(realComputableShiftedRawDCT.laws.D.algebra_laws
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)).component_smul,
      hx]
  have hWhisker := tensorCoefficient_hom_one
    ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
    (Z.atom l).label sOuter (Z.atom l).shift P₁
    sourceABCD rowLast xAssoc hxNorm
  have hRawSmul :
      rawReal.C.leftCoeff
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
          (Z.atom l).label rowLast sourceABCD xAssoc
          (rawReal.D.algebra (Z.atom l).label).one =
        (rawReal.D.algebra
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label)).smul
          (RawDCT.paritySign
            (shiftedReal.C.rowParity
                (W.atom i).label (X.atom j).label ab * (Y.atom k).shift))
          (rawReal.C.leftCoeff
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
            (Z.atom l).label rowLast sourceABCD
            (Associator.homCoefficient shiftedReal
              (W.atom i).label (X.atom j).label (Y.atom k).label
              ab abc bc a_bc)
            (rawReal.D.algebra (Z.atom l).label).one) := by
    dsimp only [xAssoc]
    exact rawLeftCoeff_smul_left rawReal.D realRawDCT.laws.D
      rawReal.C realRawDCT.laws.C _ _ _ _ _ _ _
  rw [hRawSmul] at hWhisker
  exact hLowered.trans hWhisker

/-- The middle top associator is the normalized connector for
`(a, b + c, d)`, transported back to the fixed left-associated total. -/
private theorem cast_topMiddleHomEntry_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    let q₁ := topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast
    let q₂ := topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let h₁ : (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (tensorObj W (tensorObj X Y)) Z q₁).label = t :=
      topFirstMiddleSlot_label W X Y Z i j k l bc a_bc rowLast
    let h₂ : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj (tensorObj X Y) Z) q₂).label = t :=
      topSecondMiddleSlot_label W X Y Z i j k l bc bc_d a_bcd
    cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) h₁)
        ((RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂).coeff
          (h₁.trans h₂.symm)) =
      let hMid :
          (W.atom i).label +
              ((X.atom j).label + (Y.atom k).label) + (Z.atom l).label = t :=
        congrArg (fun q => q + (Z.atom l).label)
          (_root_.add_assoc (W.atom i).label
            (X.atom j).label (Y.atom k).label).symm
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hMid)
        ((shiftedReal.D.algebra
          ((W.atom i).label +
            ((X.atom j).label + (Y.atom k).label) +
            (Z.atom l).label)).smul
          (RawDCT.paritySign
            (shiftedReal.C.rowParity (W.atom i).label
                ((X.atom j).label + (Y.atom k).label) a_bc *
              (Z.atom l).shift))
          (Associator.homCoefficient shiftedReal
            (W.atom i).label
            ((X.atom j).label + (Y.atom k).label)
            (Z.atom l).label
            a_bc
            (Associator.castIndex shiftedReal
              (_root_.add_assoc (W.atom i).label
                (X.atom j).label (Y.atom k).label) rfl rowLast)
            bc_d a_bcd)) := by
  dsimp only
  let q₁ := topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast
  let q₂ := topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd
  let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let h₁ := topFirstMiddleSlot_label W X Y Z i j k l bc a_bc rowLast
  let h₂ := topSecondMiddleSlot_label W X Y Z i j k l bc bc_d a_bcd
  let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    X Y (binarySlot X Y j k bc)
  let hBC := binarySlot_position_label X Y j k bc
  let a_bc' := Associator.castIndex shiftedReal rfl hBC.symm a_bc
  let hABC :
      (W.atom i).label + (X.atom j).label + (Y.atom k).label =
        (W.atom i).label + ((tensorObj X Y).atom pBC).label :=
    (_root_.add_assoc (W.atom i).label (X.atom j).label
      (Y.atom k).label).trans
        (congrArg (fun q => (W.atom i).label + q) hBC.symm)
  let rowLast' := Associator.castIndex shiftedReal hABC rfl rowLast
  let bc_d' := Associator.castIndex shiftedReal hBC.symm rfl bc_d
  let hBCD :
      (X.atom j).label + (Y.atom k).label + (Z.atom l).label =
        ((tensorObj X Y).atom pBC).label + (Z.atom l).label :=
    congrArg (fun q => q + (Z.atom l).label) hBC.symm
  let a_bcd' := Associator.castIndex shiftedReal rfl hBCD a_bcd
  let qL := RealAssociatorLaws.leftRouteSlot W (tensorObj X Y) Z
    i pBC l a_bc' rowLast'
  let qR := RealAssociatorLaws.rightRouteSlot W (tensorObj X Y) Z
    i pBC l bc_d' a_bcd'
  have hq₁ : q₁ = qL := topFirstMiddleSlot_as_outerLeftRoute
    W X Y Z i j k l bc a_bc rowLast
  have hq₂ : q₂ = qR := topSecondMiddleSlot_as_outerRightRoute
    W X Y Z i j k l bc bc_d a_bcd
  let hMid := congrArg (fun q => q + (Z.atom l).label)
    (_root_.add_assoc (W.atom i).label (X.atom j).label
      (Y.atom k).label).symm
  let hBCTotal := congrArg
    (fun q => (W.atom i).label + q + (Z.atom l).label) hBC
  let hTotal :
      (W.atom i).label + ((tensorObj X Y).atom pBC).label +
          (Z.atom l).label = t := hBCTotal.trans hMid
  let hL := RealAssociatorLaws.leftRouteSlot_label
    W (tensorObj X Y) Z i pBC l a_bc' rowLast'
  let hR := RealAssociatorLaws.rightRouteSlot_label
    W (tensorObj X Y) Z i pBC l bc_d' a_bcd'
  let hLT : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z qL).label = t := hL.trans hTotal
  let hRT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj (tensorObj X Y) Z) qR).label = t :=
    hR.trans ((_root_.add_assoc (W.atom i).label
      ((tensorObj X Y).atom pBC).label (Z.atom l).label).symm.trans hTotal)
  have hSlots := cast_homEntry_coeff_of_slots_eq
    W (tensorObj X Y) Z q₁ qL q₂ qR hq₁ hq₂ t h₁ h₂ hLT hRT
  have hNorm := cast_normalizedHomEntry_route_coeff
    W (tensorObj X Y) Z i pBC l
      a_bc' rowLast' bc_d' a_bcd' t hTotal
  rw [hSlots]
  rw [hNorm]
  have hCastSplit
      (u : (shiftedReal.D.algebra
        ((W.atom i).label + ((tensorObj X Y).atom pBC).label +
          (Z.atom l).label)).carrier) :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hTotal) u =
        cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hMid)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              hBCTotal) u) := by
    rw [show hTotal = hBCTotal.trans hMid by apply Subsingleton.elim]
    exact (cast_cast_route
      (congrArg (fun q : ZMod 8 =>
        (shiftedReal.D.algebra q).carrier) hBCTotal)
      (congrArg (fun q : ZMod 8 =>
        (shiftedReal.D.algebra q).carrier) hMid) u).symm
  rw [hCastSplit]
  rw [cast_smul shiftedReal.D hBCTotal]
  have hParity : shiftedReal.C.rowParity (W.atom i).label
      ((tensorObj X Y).atom pBC).label a_bc' =
        shiftedReal.C.rowParity (W.atom i).label
          ((X.atom j).label + (Y.atom k).label) a_bc := by
    simpa only [a_bc'] using rowParity_castIndex rfl hBC.symm a_bc
  rw [hParity]
  let rowLastCanonical := Associator.castIndex shiftedReal
    (_root_.add_assoc (W.atom i).label (X.atom j).label
      (Y.atom k).label) rfl rowLast
  have hRowLast : rowLast' = Associator.castIndex shiftedReal
      (congrArg (fun q => (W.atom i).label + q) hBC).symm rfl
      rowLastCanonical := by
    dsimp only [rowLast', rowLastCanonical]
    rw [castIndex_trans]
  have hSecond := cast_homCoefficient_second_label hBC
    a_bc rowLastCanonical bc_d a_bcd
  rw [← hRowLast] at hSecond
  have hSecond' :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
          hBCTotal)
        (Associator.homCoefficient shiftedReal
          (W.atom i).label ((tensorObj X Y).atom pBC).label
          (Z.atom l).label a_bc' rowLast' bc_d' a_bcd') =
      Associator.homCoefficient shiftedReal
        (W.atom i).label ((X.atom j).label + (Y.atom k).label)
        (Z.atom l).label a_bc rowLastCanonical bc_d a_bcd := by
    simpa only [hBCTotal, a_bc', bc_d', a_bcd', hBCD] using hSecond
  rw [hSecond']

/-- The source atom of a supported ternary associator entry has the shift
obtained by adding the three object shifts and its two source-row parities. -/
private theorem leftRouteSlot_totalShift (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj X Y) Z
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc)).shift =
        (X.atom i).shift + (Y.atom j).shift +
          shiftedReal.C.rowParity
            (X.atom i).label (Y.atom j).label ab +
          (Z.atom k).shift +
          shiftedReal.C.rowParity
            ((X.atom i).label + (Y.atom j).label) (Z.atom k).label abc := by
  let hInner := RealAssociatorLaws.leftRouteSlot_innerLabel
    X Y Z i j k ab abc
  have hInnerShift :
      ((tensorObj X Y).atom
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).left).shift =
        (X.atom i).shift + (Y.atom j).shift +
          shiftedReal.C.rowParity
            (X.atom i).label (Y.atom j).label ab := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        (RealAssociatorLaws.leftRouteSlot X Y Z
          i j k ab abc).left)).shift = _
    rw [RealAssociatorLaws.leftRouteSlot_inner]
    rfl
  have hOuterParity :
      shiftedReal.C.rowParity
          ((tensorObj X Y).atom
            (RealAssociatorLaws.leftRouteSlot X Y Z
              i j k ab abc).left).label
          (Z.atom (RealAssociatorLaws.leftRouteSlot X Y Z
            i j k ab abc).right).label
          (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).fusion =
        shiftedReal.C.rowParity
          ((X.atom i).label + (Y.atom j).label) (Z.atom k).label abc := by
    have h := rowParity_castIndex hInner rfl
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).fusion
    rw [RealAssociatorLaws.leftRouteSlot_outerRow] at h
    exact h.symm
  change ((tensorObj X Y).atom
      (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).left).shift +
      (Z.atom (RealAssociatorLaws.leftRouteSlot X Y Z
        i j k ab abc).right).shift +
      shiftedReal.C.rowParity
        ((tensorObj X Y).atom
          (RealAssociatorLaws.leftRouteSlot X Y Z
            i j k ab abc).left).label
        (Z.atom (RealAssociatorLaws.leftRouteSlot X Y Z
          i j k ab abc).right).label
        (RealAssociatorLaws.leftRouteSlot X Y Z i j k ab abc).fusion = _
  rw [hInnerShift, hOuterParity]
  rfl

/-- The target atom of the same entry has the analogous two target-row
parities.  These two endpoint formulas will be combined with the existing
connector-grade theorem, not with a fourfold table computation. -/
private theorem rightRouteSlot_totalShift (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index
      (X.atom i).label ((Y.atom j).label + (Z.atom k).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C X
      (tensorObj Y Z)
      (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc)).shift =
        (X.atom i).shift + (Y.atom j).shift + (Z.atom k).shift +
          shiftedReal.C.rowParity
            (Y.atom j).label (Z.atom k).label bc +
          shiftedReal.C.rowParity (X.atom i).label
            ((Y.atom j).label + (Z.atom k).label) a_bc := by
  let hInner := RealAssociatorLaws.rightRouteSlot_innerLabel
    X Y Z i j k bc a_bc
  have hInnerShift :
      ((tensorObj Y Z).atom
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).right).shift =
        (Y.atom j).shift + (Z.atom k).shift +
          shiftedReal.C.rowParity
            (Y.atom j).label (Z.atom k).label bc := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z
      ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
        (RealAssociatorLaws.rightRouteSlot X Y Z
          i j k bc a_bc).right)).shift = _
    rw [RealAssociatorLaws.rightRouteSlot_inner]
    rfl
  have hOuterParity :
      shiftedReal.C.rowParity
          (X.atom (RealAssociatorLaws.rightRouteSlot X Y Z
            i j k bc a_bc).left).label
          ((tensorObj Y Z).atom
            (RealAssociatorLaws.rightRouteSlot X Y Z
              i j k bc a_bc).right).label
          (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).fusion =
        shiftedReal.C.rowParity (X.atom i).label
          ((Y.atom j).label + (Z.atom k).label) a_bc := by
    have h := rowParity_castIndex rfl hInner
      (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).fusion
    rw [RealAssociatorLaws.rightRouteSlot_outerRow] at h
    exact h.symm
  change (X.atom (RealAssociatorLaws.rightRouteSlot X Y Z
      i j k bc a_bc).left).shift +
      ((tensorObj Y Z).atom
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).right).shift +
      shiftedReal.C.rowParity
        (X.atom (RealAssociatorLaws.rightRouteSlot X Y Z
          i j k bc a_bc).left).label
        ((tensorObj Y Z).atom
          (RealAssociatorLaws.rightRouteSlot X Y Z
            i j k bc a_bc).right).label
        (RealAssociatorLaws.rightRouteSlot X Y Z i j k bc a_bc).fusion = _
  rw [hInnerShift, hOuterParity]
  rw [RealAssociatorLaws.rightRouteSlot_left]
  ac_rfl

/-- The final, left-whiskered associator entry is the stored ternary
connector on `(b,c,d)`, with the outer identity and endpoint twist reduced. -/
private theorem cast_topFinalTensorEntry_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    let q₂ := topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let h₂ := topSecondMiddleSlot_label W X Y Z i j k l bc bc_d a_bcd
    let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z)) qT).label = t :=
      (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
        ((_root_.add_assoc (W.atom i).label (X.atom j).label
          ((Y.atom k).label + (Z.atom l).label)).symm.trans
         (_root_.add_assoc ((W.atom i).label + (X.atom j).label)
          (Y.atom k).label (Z.atom l).label).symm)
    let P₃ := rawReal.T.parity
        (X.atom j).label (Y.atom k).label (Z.atom l).label +
      rawRowParityOfShifted (X.atom j).label (Y.atom k).label bc +
      rawRowParityOfShifted
        ((X.atom j).label + (Y.atom k).label) (Z.atom l).label bc_d +
      rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd +
      rawRowParityOfShifted (X.atom j).label
        ((Y.atom k).label + (Z.atom l).label) bcd
    cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) h₂)
        ((Tensor.entry shiftedReal.D shiftedReal.C
          (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT).coeff
            (h₂.trans hT.symm)) =
      let hAssoc := (show (W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label =
          (W.atom i).label +
            ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
          by ac_rfl).symm
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc)
        ((shiftedReal.D.algebra ((W.atom i).label +
          ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))).smul
          (RawDCT.paritySign
            (shiftNu realComputableNuBeta.data (W.atom i).label
              ((X.atom j).label + (Y.atom k).label + (Z.atom l).label) * P₃))
          ((shiftedReal.D.algebra ((W.atom i).label +
            ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))).smul
            (RawDCT.paritySign
              (shiftedReal.C.rowParity
                (X.atom j).label (Y.atom k).label bc * (Z.atom l).shift))
            (rawReal.C.leftCoeff (W.atom i).label
              ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
              targetABCD a_bcd (rawReal.D.algebra (W.atom i).label).one
              (Associator.homCoefficient shiftedReal
                (X.atom j).label (Y.atom k).label (Z.atom l).label
                bc bc_d cd bcd)))) := by
  dsimp only
  let q₂ : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj (tensorObj X Y) Z) :=
    topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd
  let qT : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) :=
    quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let h₂ := topSecondMiddleSlot_label W X Y Z i j k l bc bc_d a_bcd
  let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) qT).label = t :=
    (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
      ((_root_.add_assoc (W.atom i).label (X.atom j).label
        ((Y.atom k).label + (Z.atom l).label)).symm.trans
       (_root_.add_assoc ((W.atom i).label + (X.atom j).label)
        (Y.atom k).label (Z.atom l).label).symm)
  let P₃ := rawReal.T.parity
        (X.atom j).label (Y.atom k).label (Z.atom l).label +
      rawRowParityOfShifted (X.atom j).label (Y.atom k).label bc +
      rawRowParityOfShifted
        ((X.atom j).label + (Y.atom k).label) (Z.atom l).label bc_d +
      rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd +
      rawRowParityOfShifted (X.atom j).label
        ((Y.atom k).label + (Z.atom l).label) bcd
  let qL := RealAssociatorLaws.leftRouteSlot X Y Z j k l bc bc_d
  let qR := RealAssociatorLaws.rightRouteSlot X Y Z j k l cd bcd
  have hGet₂ :
      (Tensor.slots shiftedReal.D shiftedReal.C (tensorObj X Y) Z).get
          q₂.right = qL := by
    simpa only [q₂, qL] using
      (topSecondMiddleSlot_inner W X Y Z i j k l bc bc_d a_bcd)
  have hGetT :
      (Tensor.slots shiftedReal.D shiftedReal.C X (tensorObj Y Z)).get
          qT.right = qR := by
    simpa only [qT, qR] using
      (quadRightSlot_inner W X Y Z i j k l cd bcd targetABCD)
  have hsLeft : q₂.left = i := by
    simpa only [q₂] using
      (topSecondMiddleSlot_left W X Y Z i j k l bc bc_d a_bcd)
  have htLeft : qT.left = i := by
    simpa only [qT] using
      (quadRightSlot_left W X Y Z i j k l cd bcd targetABCD)
  let hA : (W.atom q₂.left).label = (W.atom qT.left).label :=
    congrArg (fun r => (W.atom r).label) (hsLeft.trans htLeft.symm)
  let hB : ((tensorObj (tensorObj X Y) Z).atom q₂.right).label =
      ((tensorObj X (tensorObj Y Z)).atom qT.right).label := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj X Y) Z
        ((Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj X Y) Z).get q₂.right)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X (tensorObj Y Z)
        ((Tensor.slots shiftedReal.D shiftedReal.C
          X (tensorObj Y Z)).get qT.right)).label
    rw [hGet₂, hGetT]
    exact RealAssociatorLaws.routeAssocLabelEq X Y Z j k l bc bc_d cd bcd
  let hLeft : (W.atom q₂.left).label = (W.atom i).label :=
    congrArg (fun r => (W.atom r).label) hsLeft
  let B := (X.atom j).label + (Y.atom k).label + (Z.atom l).label
  let hRight : ((tensorObj (tensorObj X Y) Z).atom q₂.right).label = B := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj X Y) Z
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (tensorObj X Y) Z).get q₂.right)).label = B
    rw [hGet₂]
    exact RealAssociatorLaws.leftRouteSlot_label X Y Z j k l bc bc_d
  let hLeftTotal :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj (tensorObj X Y) Z) q₂).label =
        (W.atom i).label +
          ((tensorObj (tensorObj X Y) Z).atom q₂.right).label :=
    congrArg (fun q => q +
      ((tensorObj (tensorObj X Y) Z).atom q₂.right).label) hLeft
  let hRightTotal : (W.atom i).label +
      ((tensorObj (tensorObj X Y) Z).atom q₂.right).label =
        (W.atom i).label + B :=
    congrArg (fun q => (W.atom i).label + q) hRight
  let hNaturalTotal := hLeftTotal.trans hRightTotal
  let hAssoc : (W.atom i).label + B = t :=
    (show (W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label =
        (W.atom i).label +
          ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
        by ac_rfl).symm
  have hTotalProof : h₂ = hNaturalTotal.trans hAssoc := Subsingleton.elim _ _
  have hCastSplit
      (u : (shiftedReal.D.algebra
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z) q₂).label).carrier) :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) h₂) u =
        cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              hRightTotal)
            (cast (congrArg
                (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
                hLeftTotal) u)) := by
    rw [hTotalProof]
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              hNaturalTotal) u) :=
        (cast_cast_route
          (congrArg (fun q : ZMod 8 =>
            (shiftedReal.D.algebra q).carrier) hNaturalTotal)
          (congrArg (fun q : ZMod 8 =>
            (shiftedReal.D.algebra q).carrier) hAssoc) u).symm
      _ = _ := congrArg
        (fun v => cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc) v)
        (by
          rw [show hNaturalTotal = hLeftTotal.trans hRightTotal by
            apply Subsingleton.elim]
          exact (cast_cast_route
            (congrArg (fun q : ZMod 8 =>
              (shiftedReal.D.algebra q).carrier) hLeftTotal)
            (congrArg (fun q : ZMod 8 =>
              (shiftedReal.D.algebra q).carrier) hRightTotal) u).symm)
  have hEntry := tensorEntry_coeff_of_label_eq
    (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
    q₂ qT hA hB (h₂.trans hT.symm)
  have hEntryCast := congrArg
    (fun u => cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
        hRightTotal)
      (cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
          hLeftTotal) u)) hEntry
  let xAssoc := (shiftedReal.D.algebra B).smul
      (RawDCT.paritySign
        (shiftedReal.C.rowParity
          (X.atom j).label (Y.atom k).label bc * (Z.atom l).shift))
      (Associator.homCoefficient shiftedReal
        (X.atom j).label (Y.atom k).label (Z.atom l).label bc bc_d cd bcd)
  have hAssocInput :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRight)
        (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB) =
      xAssoc := by
    change cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRight)
      ((RealAssociator.homEntry X Y Z
        ((Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj X Y) Z).get q₂.right)
        ((Tensor.slots shiftedReal.D shiftedReal.C
          X (tensorObj Y Z)).get qT.right)).coeff hB) = xAssoc
    let hTarget :
        (Tensor.slotAtom shiftedReal.D shiftedReal.C X (tensorObj Y Z)
          ((Tensor.slots shiftedReal.D shiftedReal.C
            X (tensorObj Y Z)).get qT.right)).label = B :=
      hB.symm.trans hRight
    let hL := RealAssociatorLaws.leftRouteSlot_label X Y Z j k l bc bc_d
    let hR := (RealAssociatorLaws.rightRouteSlot_label
      X Y Z j k l cd bcd).trans
        (_root_.add_assoc (X.atom j).label (Y.atom k).label
          (Z.atom l).label).symm
    have hp : hB = hRight.trans hTarget.symm := Subsingleton.elim _ _
    rw [hp]
    have hSlots := cast_homEntry_coeff_of_slots_eq X Y Z
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (tensorObj X Y) Z).get q₂.right) qL
      ((Tensor.slots shiftedReal.D shiftedReal.C
        X (tensorObj Y Z)).get qT.right) qR
      hGet₂ hGetT B hRight hTarget hL hR
    have hRoute := RealAssociatorNaturality.realHomEntry_route_coeff
      X Y Z j k l bc bc_d cd bcd
    have hRouteNormalized :
        cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hL)
          ((RealAssociator.homEntry X Y Z qL qR).coeff
            (hL.trans hR.symm)) = xAssoc := by
      rw [show hL.trans hR.symm =
          RealAssociatorLaws.routeAssocLabelEq X Y Z j k l bc bc_d cd bcd by
        apply Subsingleton.elim]
      dsimp only [qL, qR]
      rw [hRoute]
      exact cast_algebra_symm_cancel shiftedReal.D hL xAssoc
    exact hSlots.trans hRouteNormalized
  let pBC := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    X Y (binarySlot X Y j k bc)
  let hBC := binarySlot_position_label X Y j k bc
  let bc_dOuter := Associator.castIndex shiftedReal hBC.symm rfl bc_d
  let hBCD : B = ((tensorObj X Y).atom pBC).label + (Z.atom l).label :=
    congrArg (fun q => q + (Z.atom l).label) hBC.symm
  let a_bcdOuter := Associator.castIndex shiftedReal rfl hBCD a_bcd
  let q₂Outer := RealAssociatorLaws.rightRouteSlot
    W (tensorObj X Y) Z i pBC l bc_dOuter a_bcdOuter
  have hq₂Outer : q₂ = q₂Outer :=
    topSecondMiddleSlot_as_outerRightRoute W X Y Z i j k l bc bc_d a_bcd
  have hSource :
      Associator.castIndex shiftedReal rfl hRight
        (Associator.castIndex shiftedReal hLeft rfl q₂.fusion) = a_bcd := by
    apply Fin.ext
    simp only [castIndex_val]
    rw [hq₂Outer]
    have hv := congrArg Fin.val
      (RealAssociatorLaws.rightRouteSlot_outerRow
        W (tensorObj X Y) Z i pBC l bc_dOuter a_bcdOuter)
    simpa only [q₂Outer, a_bcdOuter, castIndex_val] using hv
  let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    Y Z (binarySlot Y Z k l cd)
  let hCD := binarySlot_position_label Y Z k l cd
  let bcdOuter := Associator.castIndex shiftedReal rfl hCD.symm bcd
  let hRest : B = (X.atom j).label + ((tensorObj Y Z).atom pCD).label :=
    (_root_.add_assoc (X.atom j).label (Y.atom k).label
      (Z.atom l).label).trans
      (congrArg (fun q => (X.atom j).label + q) hCD.symm)
  let targetOuter := Associator.castIndex shiftedReal rfl hRest targetABCD
  let qTOuter := RealAssociatorLaws.rightRouteSlot
    W X (tensorObj Y Z) i j pCD bcdOuter targetOuter
  have hqTOuter : qT = qTOuter :=
    quadRightSlot_as_outerRightRoute W X Y Z i j k l cd bcd targetABCD
  have hTarget :
      Associator.castIndex shiftedReal rfl hRight
        (Associator.castIndex shiftedReal hLeft rfl
          (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion)) =
      targetABCD := by
    apply Fin.ext
    simp only [castIndex_val]
    rw [hqTOuter]
    have hv := congrArg Fin.val
      (RealAssociatorLaws.rightRouteSlot_outerRow
        W X (tensorObj Y Z) i j pCD bcdOuter targetOuter)
    simpa only [qTOuter, targetOuter, castIndex_val] using hv
  have hId :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
        (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA) =
      (shiftedReal.D.algebra (W.atom i).label).one := by
    exact cast_homId_coeff shiftedReal.D W q₂.left qT.left
      (hsLeft.trans htLeft.symm) hA (W.atom i).label hLeft
  let sOuter := (W.atom q₂.left).shift
  let tSource := ((tensorObj (tensorObj X Y) Z).atom q₂.right).shift
  let tTarget := ((tensorObj X (tensorObj Y Z)).atom qT.right).shift
  let A := (W.atom i).label
  have hLeftCoefficient := tensorCoefficient_cast_left_label
    (W.atom q₂.left).label A
    ((tensorObj (tensorObj X Y) Z).atom q₂.right).label hLeft
    sOuter tSource tTarget q₂.fusion
    (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion)
    (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA)
    (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)
  have hLeftTransport :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeftTotal)
        (Tensor.coefficient shiftedReal.D shiftedReal.C
          (W.atom q₂.left).label
          ((tensorObj (tensorObj X Y) Z).atom q₂.right).label
          sOuter tSource tTarget q₂.fusion
          (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion)
          (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA)
          (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)) =
        Tensor.coefficient shiftedReal.D shiftedReal.C
          A ((tensorObj (tensorObj X Y) Z).atom q₂.right).label
          sOuter tSource tTarget
          (Associator.castIndex shiftedReal hLeft rfl q₂.fusion)
          (Associator.castIndex shiftedReal hLeft rfl
            (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
            (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA))
          (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB) := by
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
            (congrArg (fun q => q +
              ((tensorObj (tensorObj X Y) Z).atom q₂.right).label) hLeft))
          (Tensor.coefficient shiftedReal.D shiftedReal.C
            (W.atom q₂.left).label
            ((tensorObj (tensorObj X Y) Z).atom q₂.right).label
            sOuter tSource tTarget q₂.fusion
            (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion)
            (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA)
            (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)) :=
        cast_proof_irrel _ _ _
      _ = _ := hLeftCoefficient
  have hEntryLeft := hEntryCast.trans
    (congrArg (fun u => cast (congrArg
      (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRightTotal) u)
      hLeftTransport)
  have hRightCoefficient := tensorCoefficient_cast_right_label
    A ((tensorObj (tensorObj X Y) Z).atom q₂.right).label B hRight
    sOuter tSource tTarget
    (Associator.castIndex shiftedReal hLeft rfl q₂.fusion)
    (Associator.castIndex shiftedReal hLeft rfl
      (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion))
    (cast (congrArg
      (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
      (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA))
    (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)
  have hRightTransport :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRightTotal)
        (Tensor.coefficient shiftedReal.D shiftedReal.C
          A ((tensorObj (tensorObj X Y) Z).atom q₂.right).label
          sOuter tSource tTarget
          (Associator.castIndex shiftedReal hLeft rfl q₂.fusion)
          (Associator.castIndex shiftedReal hLeft rfl
            (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
            (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA))
          (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)) =
        Tensor.coefficient shiftedReal.D shiftedReal.C A B
          sOuter tSource tTarget
          (Associator.castIndex shiftedReal rfl hRight
            (Associator.castIndex shiftedReal hLeft rfl q₂.fusion))
          (Associator.castIndex shiftedReal rfl hRight
            (Associator.castIndex shiftedReal hLeft rfl
              (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion)))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
            (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA))
          (cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hRight)
            (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)) := by
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
            (congrArg (fun q => A + q) hRight))
          (Tensor.coefficient shiftedReal.D shiftedReal.C
            A ((tensorObj (tensorObj X Y) Z).atom q₂.right).label
            sOuter tSource tTarget
            (Associator.castIndex shiftedReal hLeft rfl q₂.fusion)
            (Associator.castIndex shiftedReal hLeft rfl
              (Associator.castIndex shiftedReal hA.symm hB.symm qT.fusion))
            (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hLeft)
              (((Hom.id shiftedReal.D W) q₂.left qT.left).coeff hA))
            (((RealAssociator.hom X Y Z) q₂.right qT.right).coeff hB)) :=
        cast_proof_irrel _ _ _
      _ = _ := hRightCoefficient
  have hEntryRight := hEntryLeft.trans hRightTransport
  rw [hSource, hTarget, hId, hAssocInput] at hEntryRight
  have hLowered :
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) h₂)
        ((Tensor.entry shiftedReal.D shiftedReal.C
          (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT).coeff
            (h₂.trans hT.symm)) =
      cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc)
        (Tensor.coefficient shiftedReal.D shiftedReal.C A B
          sOuter tSource tTarget a_bcd targetABCD
          (shiftedReal.D.algebra A).one xAssoc) := by
    calc
      _ = cast (congrArg
            (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc)
          (cast (congrArg
              (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
              hRightTotal)
            (cast (congrArg
                (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier)
                hLeftTotal)
              ((Tensor.entry shiftedReal.D shiftedReal.C
                (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
                q₂ qT).coeff (h₂.trans hT.symm)))) := hCastSplit _
      _ = _ := congrArg
        (fun u => cast (congrArg
          (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc) u)
        (by simpa only [A, B, sOuter, tSource, tTarget] using hEntryRight)
  have hx := realShiftedHomCoefficient_memGrade_raw
    (X.atom j).label (Y.atom k).label (Z.atom l).label bc bc_d cd bcd
  have hxNorm : (shiftedReal.D.algebra B).MemGrade P₃ xAssoc := by
    dsimp only [xAssoc]
    unfold SuperAlgebraData.MemGrade at hx ⊢
    rw [(realComputableShiftedRawDCT.laws.D.algebra_laws B).component_smul,
      hx]
  have hSourceShift : tSource =
      (X.atom j).shift + (Y.atom k).shift +
        shiftedReal.C.rowParity (X.atom j).label (Y.atom k).label bc +
        (Z.atom l).shift +
        shiftedReal.C.rowParity
          ((X.atom j).label + (Y.atom k).label) (Z.atom l).label bc_d := by
    dsimp only [tSource]
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj X Y) Z
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (tensorObj X Y) Z).get q₂.right)).shift = _
    rw [hGet₂]
    exact leftRouteSlot_totalShift X Y Z j k l bc bc_d
  have hTargetShift : tTarget =
      (X.atom j).shift + (Y.atom k).shift + (Z.atom l).shift +
        shiftedReal.C.rowParity (Y.atom k).label (Z.atom l).label cd +
        shiftedReal.C.rowParity (X.atom j).label
          ((Y.atom k).label + (Z.atom l).label) bcd := by
    dsimp only [tTarget]
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C X (tensorObj Y Z)
      ((Tensor.slots shiftedReal.D shiftedReal.C
        X (tensorObj Y Z)).get qT.right)).shift = _
    rw [hGetT]
    exact rightRouteSlot_totalShift X Y Z j k l cd bcd
  have hEndpoint : tSource + tTarget = P₃ := by
    rw [hSourceShift, hTargetShift]
    calc
      _ = shiftedReal.C.rowParity
            (X.atom j).label (Y.atom k).label bc +
          shiftedReal.C.rowParity
            ((X.atom j).label + (Y.atom k).label) (Z.atom l).label bc_d +
          shiftedReal.C.rowParity
            (Y.atom k).label (Z.atom l).label cd +
          shiftedReal.C.rowParity (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label) bcd := by
        have hcancel : ∀ x y p z q r s : ZMod 2,
            x + y + p + z + q + (x + y + z + r + s) =
              p + q + r + s := by decide +revert
        exact hcancel _ _ _ _ _ _ _
      _ = P₃ := shiftedConnectorRowSum_eq_rawGrade
        (X.atom j).label (Y.atom k).label (Z.atom l).label bc bc_d cd bcd
  have hWhisker := tensorCoefficient_one_hom_of_endpoint_sum
    A B sOuter tSource tTarget P₃ a_bcd targetABCD xAssoc hxNorm hEndpoint
  have hRawSmul :
      rawReal.C.leftCoeff A B targetABCD a_bcd
          (rawReal.D.algebra A).one xAssoc =
        (rawReal.D.algebra (A + B)).smul
          (RawDCT.paritySign
            (shiftedReal.C.rowParity
              (X.atom j).label (Y.atom k).label bc * (Z.atom l).shift))
          (rawReal.C.leftCoeff A B targetABCD a_bcd
            (rawReal.D.algebra A).one
            (Associator.homCoefficient shiftedReal
              (X.atom j).label (Y.atom k).label (Z.atom l).label
              bc bc_d cd bcd)) := by
    dsimp only [xAssoc]
    exact rawLeftCoeff_smul_right rawReal.D realRawDCT.laws.D
      rawReal.C realRawDCT.laws.C _ _ _ _ _ _ _
  rw [hRawSmul] at hWhisker
  exact hLowered.trans
    (congrArg
      (fun u => cast (congrArg
        (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hAssoc) u)
      hWhisker)

private theorem exists_eq_topFirstMiddleSlot (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z) :
    ∃ (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size)
      (l : Fin Z.size)
      (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
      (a_bc : shiftedReal.C.Index (W.atom i).label
        ((X.atom j).label + (Y.atom k).label))
      (rowLast : shiftedReal.C.Index
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
        (Z.atom l).label),
      q = topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast := by
  let c := (RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
    W (tensorObj X Y) Z).symm q
  have hrecover := (RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
    W (tensorObj X Y) Z).apply_symm_apply q
  rcases hc : c with ⟨qInner, l, outer⟩
  rcases RealAssociatorLaws.exists_eq_rightRouteSlot W X Y qInner with
    ⟨i, j, k, bc, a_bc, hInnerSlot⟩
  subst qInner
  let hInner := RealAssociatorLaws.rightRouteSlot_label
    W X Y i j k bc a_bc
  let hCanonical := (_root_.add_assoc (W.atom i).label (X.atom j).label
    (Y.atom k).label).trans hInner.symm
  let rowLast := Associator.castIndex shiftedReal hCanonical.symm rfl outer
  refine ⟨i, j, k, l, bc, a_bc, rowLast, ?_⟩
  have hc' : c = ⟨RealAssociatorLaws.rightRouteSlot W X Y
      i j k bc a_bc, l, outer⟩ := hc
  calc
    q = RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z
        ⟨RealAssociatorLaws.rightRouteSlot W X Y i j k bc a_bc,
          l, outer⟩ := by rw [← hc', hrecover]
    _ = topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast := by
      unfold topFirstMiddleSlot
      dsimp only [hInner, hCanonical, rowLast]
      rw [castIndex_symm_cancel]

private theorem exists_eq_topSecondMiddleSlot (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj (tensorObj X Y) Z)) :
    ∃ (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size)
      (l : Fin Z.size)
      (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
      (bc_d : shiftedReal.C.Index
        ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
      (a_bcd : shiftedReal.C.Index (W.atom i).label
        ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)),
      q = topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd := by
  let c := (RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
    W (tensorObj X Y) Z).symm q
  have hrecover := (RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
    W (tensorObj X Y) Z).apply_symm_apply q
  rcases hc : c with ⟨i, qInner, outer⟩
  rcases RealAssociatorLaws.exists_eq_leftRouteSlot X Y Z qInner with
    ⟨j, k, l, bc, bc_d, hInnerSlot⟩
  subst qInner
  let hInner := RealAssociatorLaws.leftRouteSlot_label
    X Y Z j k l bc bc_d
  let a_bcd := Associator.castIndex shiftedReal rfl hInner outer
  refine ⟨i, j, k, l, bc, bc_d, a_bcd, ?_⟩
  have hc' : c = ⟨i, RealAssociatorLaws.leftRouteSlot X Y Z
      j k l bc bc_d, outer⟩ := hc
  calc
    q = RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z
        ⟨i, RealAssociatorLaws.leftRouteSlot X Y Z
          j k l bc bc_d, outer⟩ := by rw [← hc', hrecover]
    _ = topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd := by
      unfold topSecondMiddleSlot
      dsimp only [hInner, a_bcd]
      rw [castIndex_symm_cancel]

/-- The first top intermediate object is enumerated by the three rows
`bc`, `a_bc`, and `rowLast`, in addition to the four exterior positions. -/
private theorem sum_topFirstMiddleSlots {M : Type*} [AddCommMonoid M]
    (W X Y Z : Obj)
    (F : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj W (tensorObj X Y)) Z → M) :
    (∑ q, F q) =
      ∑ i : Fin W.size, ∑ j : Fin X.size, ∑ k : Fin Y.size,
      ∑ bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label,
      ∑ a_bc : shiftedReal.C.Index (W.atom i).label
          ((X.atom j).label + (Y.atom k).label),
      ∑ l : Fin Z.size,
      ∑ rowLast : shiftedReal.C.Index
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
          (Z.atom l).label,
        F (topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast) := by
  classical
  rw [RealAssociatorLaws.sum_leftSlotCoordinates]
  rw [RealAssociatorLaws.sum_rightSlotCoordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [RealAssociatorLaws.sum_slots X Y]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro bc _
  let hBC :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
        (binarySlot X Y j k bc)).label =
        (X.atom j).label + (Y.atom k).label := by
    rfl
  let eA : shiftedReal.C.Index (W.atom i).label
        ((X.atom j).label + (Y.atom k).label) ≃
      shiftedReal.C.Index (W.atom i).label
        (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
          (binarySlot X Y j k bc)).label :=
    Equiv.cast (congrArg₂ shiftedReal.C.Index rfl hBC.symm)
  let G := fun a_bc : shiftedReal.C.Index (W.atom i).label
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
        (binarySlot X Y j k bc)).label =>
    let qInner := RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
      W X Y ⟨i, binarySlot X Y j k bc, a_bc⟩
    ∑ l : Fin Z.size,
      ∑ rowLast : shiftedReal.C.Index
          (Tensor.slotAtom shiftedReal.D shiftedReal.C W (tensorObj X Y)
            qInner).label (Z.atom l).label,
        F (RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
          W (tensorObj X Y) Z ⟨qInner, l, rowLast⟩)
  change (∑ a_bc, G a_bc) = _
  calc
    (∑ a_bc, G a_bc) =
        ∑ a_bc : shiftedReal.C.Index (W.atom i).label
            ((X.atom j).label + (Y.atom k).label), G (eA a_bc) :=
      (eA.sum_comp G).symm
    _ = _ := by
      dsimp only [G, eA, hBC]
      apply Finset.sum_congr rfl
      intro a_bc _
      apply Finset.sum_congr rfl
      intro l _
      have heA : eA a_bc = a_bc := by
        rfl
      rw [heA]
      rw [show
        RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
            W X Y ⟨i, binarySlot X Y j k bc, a_bc⟩ =
          RealAssociatorLaws.rightRouteSlot W X Y i j k bc a_bc by
        simpa only [binarySlot] using
          (RealAssociatorLaws.rightSlotPack_route
            W X Y i j k bc a_bc)]
      let qInner := RealAssociatorLaws.rightRouteSlot W X Y i j k bc a_bc
      let hInner := RealAssociatorLaws.rightRouteSlot_label
        W X Y i j k bc a_bc
      let e : shiftedReal.C.Index
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
            (Z.atom l).label ≃
          shiftedReal.C.Index
            (Tensor.slotAtom shiftedReal.D shiftedReal.C W (tensorObj X Y)
              qInner).label (Z.atom l).label :=
        Equiv.cast (congrArg₂ shiftedReal.C.Index
          ((_root_.add_assoc (W.atom i).label (X.atom j).label
            (Y.atom k).label).trans hInner.symm) rfl)
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro rowLast _
      rfl

/-- The second top intermediate object is enumerated by `bc`, `bc_d`, and
`a_bcd`; the shared `bc` row will be forced by middle-associator support. -/
private theorem sum_topSecondMiddleSlots {M : Type*} [AddCommMonoid M]
    (W X Y Z : Obj)
    (F : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj (tensorObj X Y) Z) → M) :
    (∑ q, F q) =
      ∑ i : Fin W.size, ∑ j : Fin X.size, ∑ k : Fin Y.size,
      ∑ l : Fin Z.size,
      ∑ bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label,
      ∑ bc_d : shiftedReal.C.Index
          ((X.atom j).label + (Y.atom k).label) (Z.atom l).label,
      ∑ a_bcd : shiftedReal.C.Index (W.atom i).label
          ((X.atom j).label + (Y.atom k).label + (Z.atom l).label),
        F (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd) := by
  classical
  rw [RealAssociatorLaws.sum_rightSlotCoordinates]
  apply Finset.sum_congr rfl
  intro i _
  rw [RealAssociatorLaws.sum_leftSlotCoordinates]
  rw [RealAssociatorLaws.sum_slots X Y]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro bc _
  let hBC :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
        (binarySlot X Y j k bc)).label =
        (X.atom j).label + (Y.atom k).label := by
    rfl
  let eBC : shiftedReal.C.Index
        ((X.atom j).label + (Y.atom k).label) (Z.atom l).label ≃
      shiftedReal.C.Index
        (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
          (binarySlot X Y j k bc)).label (Z.atom l).label :=
    Equiv.cast (congrArg₂ shiftedReal.C.Index hBC.symm rfl)
  let G := fun bc_d : shiftedReal.C.Index
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
        (binarySlot X Y j k bc)).label (Z.atom l).label =>
    let qInner := RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
      X Y Z ⟨binarySlot X Y j k bc, l, bc_d⟩
    ∑ a_bcd : shiftedReal.C.Index (W.atom i).label
        (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj X Y) Z
          qInner).label,
      F (RealAssociatorLaws.rightSlotPack shiftedReal.D shiftedReal.C
        W (tensorObj X Y) Z ⟨i, qInner, a_bcd⟩)
  change (∑ bc_d, G bc_d) = _
  calc
    (∑ bc_d, G bc_d) =
        ∑ bc_d : shiftedReal.C.Index
            ((X.atom j).label + (Y.atom k).label) (Z.atom l).label,
          G (eBC bc_d) := (eBC.sum_comp G).symm
    _ = _ := by
      dsimp only [G, eBC, hBC]
      apply Finset.sum_congr rfl
      intro bc_d _
      have heBC : eBC bc_d = bc_d := by
        rfl
      rw [heBC]
      rw [show
        RealAssociatorLaws.leftSlotPack shiftedReal.D shiftedReal.C
            X Y Z ⟨binarySlot X Y j k bc, l, bc_d⟩ =
          RealAssociatorLaws.leftRouteSlot X Y Z j k l bc bc_d by
        simpa only [binarySlot] using
          (RealAssociatorLaws.leftSlotPack_route
            X Y Z j k l bc bc_d)]
      let qInner := RealAssociatorLaws.leftRouteSlot X Y Z j k l bc bc_d
      let hInner := RealAssociatorLaws.leftRouteSlot_label
        X Y Z j k l bc bc_d
      let e : shiftedReal.C.Index (W.atom i).label
            ((X.atom j).label + (Y.atom k).label + (Z.atom l).label) ≃
          shiftedReal.C.Index (W.atom i).label
            (Tensor.slotAtom shiftedReal.D shiftedReal.C (tensorObj X Y) Z
              qInner).label :=
        Equiv.cast (congrArg₂ shiftedReal.C.Index rfl hInner.symm)
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro a_bcd _
      rfl

/-! ### Support of the three top edges -/

private theorem topFirstEntry_zero_of_first_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j').label (Y.atom k').label)
    (a_bc : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i').label + (X.atom j').label + (Y.atom k').label)
      (Z.atom l').label)
    (h : i ≠ i') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
        (quadLeftSlot W X Y Z i j k l ab abc sourceABCD)
        (topFirstMiddleSlot W X Y Z i' j' k' l' bc a_bc rowLast) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold RealAssociator.hom
  apply RealAssociatorNaturality.realHomEntry_zero_of_left_ne
  intro hp
  apply h
  rw [quadLeftSlot_inner, topFirstMiddleSlot_inner] at hp
  rw [RealAssociatorLaws.leftRouteSlot_inner,
    RealAssociatorLaws.rightRouteSlot_left] at hp
  change i = i' at hp
  exact hp

private theorem topFirstEntry_zero_of_middle_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j').label (Y.atom k').label)
    (a_bc : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i').label + (X.atom j').label + (Y.atom k').label)
      (Z.atom l').label)
    (h : j ≠ j') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
        (quadLeftSlot W X Y Z i j k l ab abc sourceABCD)
        (topFirstMiddleSlot W X Y Z i' j' k' l' bc a_bc rowLast) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold RealAssociator.hom
  apply RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
  intro hp
  apply h
  rw [quadLeftSlot_inner, topFirstMiddleSlot_inner] at hp
  rw [RealAssociatorLaws.leftRouteSlot_inner,
    RealAssociatorLaws.rightRouteSlot_inner] at hp
  change j = j' at hp
  exact hp

private theorem topFirstEntry_zero_of_third_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j').label (Y.atom k').label)
    (a_bc : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i').label + (X.atom j').label + (Y.atom k').label)
      (Z.atom l').label)
    (h : k ≠ k') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
        (quadLeftSlot W X Y Z i j k l ab abc sourceABCD)
        (topFirstMiddleSlot W X Y Z i' j' k' l' bc a_bc rowLast) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold RealAssociator.hom
  apply RealAssociatorNaturality.realHomEntry_zero_of_right_ne
  intro hp
  apply h
  rw [quadLeftSlot_inner, topFirstMiddleSlot_inner] at hp
  rw [RealAssociatorLaws.leftRouteSlot_right,
    RealAssociatorLaws.rightRouteSlot_inner] at hp
  change k = k' at hp
  exact hp

private theorem topFirstEntry_zero_of_fourth_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j').label (Y.atom k').label)
    (a_bc : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i').label + (X.atom j').label + (Y.atom k').label)
      (Z.atom l').label)
    (h : l ≠ l') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
        (quadLeftSlot W X Y Z i j k l ab abc sourceABCD)
        (topFirstMiddleSlot W X Y Z i' j' k' l' bc a_bc rowLast) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  simpa [Hom.id, h, quadLeftSlot_right, topFirstMiddleSlot_right]

private theorem topLastEntry_zero_of_first_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k').label (Z.atom l').label)
    (bcd : shiftedReal.C.Index (X.atom j').label
      ((Y.atom k').label + (Z.atom l').label))
    (targetABCD : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label + (Z.atom l').label))
    (h : i ≠ i') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
        (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd)
        (quadRightSlot W X Y Z i' j' k' l' cd bcd targetABCD) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_left_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  simpa [Hom.id, h, topSecondMiddleSlot_left, quadRightSlot_left]

private theorem topLastEntry_zero_of_middle_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k').label (Z.atom l').label)
    (bcd : shiftedReal.C.Index (X.atom j').label
      ((Y.atom k').label + (Z.atom l').label))
    (targetABCD : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label + (Z.atom l').label))
    (h : j ≠ j') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
        (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd)
        (quadRightSlot W X Y Z i' j' k' l' cd bcd targetABCD) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold RealAssociator.hom
  apply RealAssociatorNaturality.realHomEntry_zero_of_left_ne
  intro hp
  apply h
  rw [topSecondMiddleSlot_inner, quadRightSlot_inner] at hp
  rw [RealAssociatorLaws.leftRouteSlot_inner,
    RealAssociatorLaws.rightRouteSlot_left] at hp
  change j = j' at hp
  exact hp

private theorem topLastEntry_zero_of_third_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k').label (Z.atom l').label)
    (bcd : shiftedReal.C.Index (X.atom j').label
      ((Y.atom k').label + (Z.atom l').label))
    (targetABCD : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label + (Z.atom l').label))
    (h : k ≠ k') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
        (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd)
        (quadRightSlot W X Y Z i' j' k' l' cd bcd targetABCD) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold RealAssociator.hom
  apply RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
  intro hp
  apply h
  rw [topSecondMiddleSlot_inner, quadRightSlot_inner] at hp
  rw [RealAssociatorLaws.leftRouteSlot_inner,
    RealAssociatorLaws.rightRouteSlot_inner] at hp
  change k = k' at hp
  exact hp

private theorem topLastEntry_zero_of_fourth_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (i' : Fin W.size) (j' : Fin X.size) (k' : Fin Y.size) (l' : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom k').label (Z.atom l').label)
    (bcd : shiftedReal.C.Index (X.atom j').label
      ((Y.atom k').label + (Z.atom l').label))
    (targetABCD : shiftedReal.C.Index (W.atom i').label
      ((X.atom j').label + (Y.atom k').label + (Z.atom l').label))
    (h : l ≠ l') :
    Tensor.entry shiftedReal.D shiftedReal.C
        (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
        (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd)
        (quadRightSlot W X Y Z i' j' k' l' cd bcd targetABCD) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply Tensor.entry_of_right_eq_zero shiftedReal.D
    realComputableShiftedRawDCT.laws.D shiftedReal.C
    realComputableShiftedRawDCT.laws.C
  unfold RealAssociator.hom
  apply RealAssociatorNaturality.realHomEntry_zero_of_right_ne
  intro hp
  apply h
  rw [topSecondMiddleSlot_inner, quadRightSlot_inner] at hp
  rw [RealAssociatorLaws.leftRouteSlot_right,
    RealAssociatorLaws.rightRouteSlot_inner] at hp
  change l = l' at hp
  exact hp

private theorem topMiddleEntry_zero_of_bc_ne (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (bc₁ bc₂ : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (hbc : bc₁ ≠ bc₂) :
    RealAssociator.homEntry W (tensorObj X Y) Z
        (topFirstMiddleSlot W X Y Z i j k l bc₁ a_bc rowLast)
        (topSecondMiddleSlot W X Y Z i j k l bc₂ bc_d a_bcd) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
  intro hp
  rw [topFirstMiddleSlot_inner, topSecondMiddleSlot_inner] at hp
  have hslot := congrArg
    (fun p => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get p) hp
  rw [RealAssociatorLaws.rightRouteSlot_inner,
    RealAssociatorLaws.leftRouteSlot_inner] at hslot
  apply hbc
  simpa only [Sigma.mk.inj_iff, heq_iff_eq, true_and] using hslot

private theorem topMiddleEntry_zero_of_first_ne (W X Y Z : Obj)
    (i₁ : Fin W.size) (j₁ : Fin X.size) (k₁ : Fin Y.size)
    (l₁ : Fin Z.size)
    (bc₁ : shiftedReal.C.Index (X.atom j₁).label (Y.atom k₁).label)
    (a_bc : shiftedReal.C.Index (W.atom i₁).label
      ((X.atom j₁).label + (Y.atom k₁).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i₁).label + (X.atom j₁).label + (Y.atom k₁).label)
      (Z.atom l₁).label)
    (i₂ : Fin W.size) (j₂ : Fin X.size) (k₂ : Fin Y.size)
    (l₂ : Fin Z.size)
    (bc₂ : shiftedReal.C.Index (X.atom j₂).label (Y.atom k₂).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j₂).label + (Y.atom k₂).label) (Z.atom l₂).label)
    (a_bcd : shiftedReal.C.Index (W.atom i₂).label
      ((X.atom j₂).label + (Y.atom k₂).label + (Z.atom l₂).label))
    (h : i₁ ≠ i₂) :
    RealAssociator.homEntry W (tensorObj X Y) Z
        (topFirstMiddleSlot W X Y Z i₁ j₁ k₁ l₁ bc₁ a_bc rowLast)
        (topSecondMiddleSlot W X Y Z i₂ j₂ k₂ l₂ bc₂ bc_d a_bcd) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply RealAssociatorNaturality.realHomEntry_zero_of_left_ne
  simpa only [topFirstMiddleSlot_inner, topSecondMiddleSlot_left,
    RealAssociatorLaws.rightRouteSlot_left] using h

private theorem topMiddleEntry_zero_of_second_ne (W X Y Z : Obj)
    (i₁ : Fin W.size) (j₁ : Fin X.size) (k₁ : Fin Y.size)
    (l₁ : Fin Z.size)
    (bc₁ : shiftedReal.C.Index (X.atom j₁).label (Y.atom k₁).label)
    (a_bc : shiftedReal.C.Index (W.atom i₁).label
      ((X.atom j₁).label + (Y.atom k₁).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i₁).label + (X.atom j₁).label + (Y.atom k₁).label)
      (Z.atom l₁).label)
    (i₂ : Fin W.size) (j₂ : Fin X.size) (k₂ : Fin Y.size)
    (l₂ : Fin Z.size)
    (bc₂ : shiftedReal.C.Index (X.atom j₂).label (Y.atom k₂).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j₂).label + (Y.atom k₂).label) (Z.atom l₂).label)
    (a_bcd : shiftedReal.C.Index (W.atom i₂).label
      ((X.atom j₂).label + (Y.atom k₂).label + (Z.atom l₂).label))
    (h : j₁ ≠ j₂) :
    RealAssociator.homEntry W (tensorObj X Y) Z
        (topFirstMiddleSlot W X Y Z i₁ j₁ k₁ l₁ bc₁ a_bc rowLast)
        (topSecondMiddleSlot W X Y Z i₂ j₂ k₂ l₂ bc₂ bc_d a_bcd) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
  intro hp
  rw [topFirstMiddleSlot_inner, topSecondMiddleSlot_inner] at hp
  have hslot := congrArg
    (fun p => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get p) hp
  rw [RealAssociatorLaws.rightRouteSlot_inner,
    RealAssociatorLaws.leftRouteSlot_inner] at hslot
  exact h (congrArg (fun q => q.left) hslot)

private theorem topMiddleEntry_zero_of_third_ne (W X Y Z : Obj)
    (i₁ : Fin W.size) (j₁ : Fin X.size) (k₁ : Fin Y.size)
    (l₁ : Fin Z.size)
    (bc₁ : shiftedReal.C.Index (X.atom j₁).label (Y.atom k₁).label)
    (a_bc : shiftedReal.C.Index (W.atom i₁).label
      ((X.atom j₁).label + (Y.atom k₁).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i₁).label + (X.atom j₁).label + (Y.atom k₁).label)
      (Z.atom l₁).label)
    (i₂ : Fin W.size) (j₂ : Fin X.size) (k₂ : Fin Y.size)
    (l₂ : Fin Z.size)
    (bc₂ : shiftedReal.C.Index (X.atom j₂).label (Y.atom k₂).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j₂).label + (Y.atom k₂).label) (Z.atom l₂).label)
    (a_bcd : shiftedReal.C.Index (W.atom i₂).label
      ((X.atom j₂).label + (Y.atom k₂).label + (Z.atom l₂).label))
    (h : k₁ ≠ k₂) :
    RealAssociator.homEntry W (tensorObj X Y) Z
        (topFirstMiddleSlot W X Y Z i₁ j₁ k₁ l₁ bc₁ a_bc rowLast)
        (topSecondMiddleSlot W X Y Z i₂ j₂ k₂ l₂ bc₂ bc_d a_bcd) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
  intro hp
  rw [topFirstMiddleSlot_inner, topSecondMiddleSlot_inner] at hp
  have hslot := congrArg
    (fun p => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get p) hp
  rw [RealAssociatorLaws.rightRouteSlot_inner,
    RealAssociatorLaws.leftRouteSlot_inner] at hslot
  exact h (congrArg (fun q => q.right) hslot)

private theorem topMiddleEntry_zero_of_fourth_ne (W X Y Z : Obj)
    (i₁ : Fin W.size) (j₁ : Fin X.size) (k₁ : Fin Y.size)
    (l₁ : Fin Z.size)
    (bc₁ : shiftedReal.C.Index (X.atom j₁).label (Y.atom k₁).label)
    (a_bc : shiftedReal.C.Index (W.atom i₁).label
      ((X.atom j₁).label + (Y.atom k₁).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i₁).label + (X.atom j₁).label + (Y.atom k₁).label)
      (Z.atom l₁).label)
    (i₂ : Fin W.size) (j₂ : Fin X.size) (k₂ : Fin Y.size)
    (l₂ : Fin Z.size)
    (bc₂ : shiftedReal.C.Index (X.atom j₂).label (Y.atom k₂).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j₂).label + (Y.atom k₂).label) (Z.atom l₂).label)
    (a_bcd : shiftedReal.C.Index (W.atom i₂).label
      ((X.atom j₂).label + (Y.atom k₂).label + (Z.atom l₂).label))
    (h : l₁ ≠ l₂) :
    RealAssociator.homEntry W (tensorObj X Y) Z
        (topFirstMiddleSlot W X Y Z i₁ j₁ k₁ l₁ bc₁ a_bc rowLast)
        (topSecondMiddleSlot W X Y Z i₂ j₂ k₂ l₂ bc₂ bc_d a_bcd) =
      AtomHom.zero shiftedReal.D _ _ := by
  apply RealAssociatorNaturality.realHomEntry_zero_of_right_ne
  simpa only [topFirstMiddleSlot_right, topSecondMiddleSlot_inner,
    RealAssociatorLaws.leftRouteSlot_right] using h

/-- After fixing the four exterior positions, top-route support leaves five
fusion rows.  In particular, the two appearances of the `X ⊗ Y` row are
the same row; this is forced by the middle associator, not by computation. -/
private theorem top_quad_slot_sum_eq_row_sum (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (hSlot := quadRouteLabelEq W X Y Z
      i j k l ab abc sourceABCD cd bcd targetABCD) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    (∑ q₁ : Tensor.Slot shiftedReal.D shiftedReal.C
          (tensorObj W (tensorObj X Y)) Z,
      ∑ q₂ : Tensor.Slot shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z),
        (AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁)
            (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT)).coeff
              hSlot) =
      ∑ bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label,
      ∑ a_bc : shiftedReal.C.Index (W.atom i).label
          ((X.atom j).label + (Y.atom k).label),
      ∑ rowLast : shiftedReal.C.Index
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
          (Z.atom l).label,
      ∑ bc_d : shiftedReal.C.Index
          ((X.atom j).label + (Y.atom k).label) (Z.atom l).label,
      ∑ a_bcd : shiftedReal.C.Index (W.atom i).label
          ((X.atom j).label + (Y.atom k).label + (Z.atom l).label),
        (AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS
              (topFirstMiddleSlot W X Y Z
                i j k l bc a_bc rowLast))
            (RealAssociator.homEntry W (tensorObj X Y) Z
              (topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast)
              (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd)))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            (topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd) qT)).coeff
              hSlot := by
  classical
  have hh : hSlot = quadRouteLabelEq W X Y Z
      i j k l ab abc sourceABCD cd bcd targetABCD := Subsingleton.elim _ _
  cases hh
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  letI : Fact (SuperAlgebraLaws
      (shiftedReal.D.algebra
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z qS).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  let F := fun
      (q₁ : Tensor.Slot shiftedReal.D shiftedReal.C
        (tensorObj W (tensorObj X Y)) Z)
      (q₂ : Tensor.Slot shiftedReal.D shiftedReal.C W
        (tensorObj (tensorObj X Y) Z)) =>
    (AtomHom.comp
      (AtomHom.comp
        (Tensor.entry shiftedReal.D shiftedReal.C
          (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁)
        (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂))
      (Tensor.entry shiftedReal.D shiftedReal.C
        (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT)).coeff
          (quadRouteLabelEq W X Y Z
            i j k l ab abc sourceABCD cd bcd targetABCD)
  change (∑ q₁, ∑ q₂, F q₁ q₂) = _
  rw [sum_topFirstMiddleSlots W X Y Z]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · rw [Fintype.sum_eq_single k]
      · apply Finset.sum_congr rfl
        intro bc _
        apply Finset.sum_congr rfl
        intro a_bc _
        rw [Fintype.sum_eq_single l]
        · apply Finset.sum_congr rfl
          intro rowLast _
          rw [sum_topSecondMiddleSlots W X Y Z]
          rw [Fintype.sum_eq_single i]
          · rw [Fintype.sum_eq_single j]
            · rw [Fintype.sum_eq_single k]
              · rw [Fintype.sum_eq_single l]
                · rw [Fintype.sum_eq_single bc]
                  · intro other hne
                    simp only [F, qS, qT]
                    simp_rw [topMiddleEntry_zero_of_bc_ne W X Y Z
                      (i := i) (j := j) (k := k) (l := l)
                      (bc₁ := bc) (bc₂ := other) (hbc := hne.symm)]
                    simp [F, qS, qT,
                      AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                      AtomHom.zero_comp realComputableShiftedRawDCT.laws.D,
                      AtomHom.coeff_zero]
                · intro other hne
                  simp only [F, qS, qT]
                  simp_rw [topLastEntry_zero_of_fourth_ne W X Y Z
                    (i := i) (j := j) (k := k) (l := other)
                    (i' := i) (j' := j) (k' := k) (l' := l)
                    (cd := cd) (bcd := bcd) (targetABCD := targetABCD)
                    (h := hne)]
                  simp [F, qS, qT,
                    AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                    AtomHom.coeff_zero]
              · intro other hne
                simp only [F, qS, qT]
                simp_rw [topLastEntry_zero_of_third_ne W X Y Z
                  (i := i) (j := j) (k := other) (i' := i) (j' := j)
                  (k' := k) (l' := l) (cd := cd) (bcd := bcd)
                  (targetABCD := targetABCD) (h := hne)]
                simp [F, qS, qT,
                  AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                  AtomHom.coeff_zero]
            · intro other hne
              simp only [F, qS, qT]
              simp_rw [topLastEntry_zero_of_middle_ne W X Y Z
                (i := i) (j := other) (i' := i) (j' := j) (k' := k)
                (l' := l) (cd := cd) (bcd := bcd)
                (targetABCD := targetABCD) (h := hne)]
              simp [F, qS, qT,
                AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                AtomHom.coeff_zero]
          · intro other hne
            simp only [F, qS, qT]
            simp_rw [topLastEntry_zero_of_first_ne W X Y Z
              (i := other) (i' := i) (j' := j) (k' := k) (l' := l)
              (cd := cd) (bcd := bcd) (targetABCD := targetABCD)
              (h := hne)]
            simp [F, qS, qT,
              AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
              AtomHom.coeff_zero]
        · intro other hne
          simp only [F, qS, qT]
          simp_rw [topFirstEntry_zero_of_fourth_ne W X Y Z
            (i := i) (j := j) (k := k) (l := l)
            (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
            (l' := other) (h := hne.symm)]
          simp [F, qS, qT,
            AtomHom.zero_comp realComputableShiftedRawDCT.laws.D,
            AtomHom.coeff_zero]
      · intro other hne
        simp only [F, qS, qT]
        simp_rw [topFirstEntry_zero_of_third_ne W X Y Z
          (i := i) (j := j) (k := k) (l := l)
          (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
          (k' := other) (h := hne.symm)]
        simp [F, qS, qT,
          AtomHom.zero_comp realComputableShiftedRawDCT.laws.D,
          AtomHom.coeff_zero]
    · intro other hne
      simp only [F, qS, qT]
      simp_rw [topFirstEntry_zero_of_middle_ne W X Y Z
        (i := i) (j := j) (k := k) (l := l)
        (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
        (j' := other) (h := hne.symm)]
      simp [F, qS, qT,
        AtomHom.zero_comp realComputableShiftedRawDCT.laws.D,
        AtomHom.coeff_zero]
  · intro other hne
    simp only [F, qS, qT]
    simp_rw [topFirstEntry_zero_of_first_ne W X Y Z
      (i := i) (j := j) (k := k) (l := l)
      (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
      (i' := other) (h := hne.symm)]
    simp [F, qS, qT,
      AtomHom.zero_comp realComputableShiftedRawDCT.laws.D,
      AtomHom.coeff_zero]

/-- A supported top-route summand transported to the canonical total is the
diagrammatic product of its final whisker, middle associator, and first
whisker coefficients. -/
private theorem cast_top_triple_comp_coeff_at_total (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (bc : shiftedReal.C.Index (X.atom j).label (Y.atom k).label)
    (a_bc : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label))
    (rowLast : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (bc_d : shiftedReal.C.Index
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label)
    (a_bcd : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let q₁ := topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast
    let q₂ := topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label
    let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
    let h₁ := topFirstMiddleSlot_label W X Y Z
      i j k l bc a_bc rowLast
    let h₂ := topSecondMiddleSlot_label W X Y Z
      i j k l bc bc_d a_bcd
    let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z)) qT).label = t :=
      (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
        (by
          exact (_root_.add_assoc (W.atom i).label (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label)).symm.trans
              (_root_.add_assoc
                ((W.atom i).label + (X.atom j).label)
                (Y.atom k).label (Z.atom l).label).symm)
    cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hS)
        ((AtomHom.comp
          (AtomHom.comp
            (Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁)
            (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT)).coeff
              (quadRouteLabelEq W X Y Z i j k l
                ab abc sourceABCD cd bcd targetABCD)) =
      (shiftedReal.D.algebra t).mul
        (cast (congrArg
          (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) h₂)
          ((Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT).coeff
              (h₂.trans hT.symm)))
        ((shiftedReal.D.algebra t).mul
          (cast (congrArg
            (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) h₁)
            ((RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂).coeff
              (h₁.trans h₂.symm)))
          (cast (congrArg
            (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hS)
            ((Tensor.entry shiftedReal.D shiftedReal.C
              (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁).coeff
                (hS.trans h₁.symm)))) := by
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let q₁ := topFirstMiddleSlot W X Y Z i j k l bc a_bc rowLast
  let q₂ := topSecondMiddleSlot W X Y Z i j k l bc bc_d a_bcd
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let t := (W.atom i).label + (X.atom j).label + (Y.atom k).label +
    (Z.atom l).label
  let hS := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
  let h₁ := topFirstMiddleSlot_label W X Y Z i j k l bc a_bc rowLast
  let h₂ := topSecondMiddleSlot_label W X Y Z i j k l bc bc_d a_bcd
  let hT : (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)) qT).label = t :=
    (quadRightSlot_label W X Y Z i j k l cd bcd targetABCD).trans
      (by
        exact (_root_.add_assoc (W.atom i).label (X.atom j).label
          ((Y.atom k).label + (Z.atom l).label)).symm.trans
            (_root_.add_assoc
              ((W.atom i).label + (X.atom j).label)
              (Y.atom k).label (Z.atom l).label).symm)
  have hp : quadRouteLabelEq W X Y Z i j k l
      ab abc sourceABCD cd bcd targetABCD = hS.trans hT.symm :=
    Subsingleton.elim _ _
  rw [hp]
  exact cast_triple_comp_coeff_at_common_label t hS h₁ h₂ hT
    (Tensor.entry shiftedReal.D shiftedReal.C
      (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁)
    (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂)
    (Tensor.entry shiftedReal.D shiftedReal.C
      (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT)

/-! ### Positions of explicit four-object slots -/

private def quadLeftPosition (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z) :
    Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size :=
  RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    (tensorObj (tensorObj W X) Y) Z q

private def quadRightPosition (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))) :
    Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size :=
  RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    W (tensorObj X (tensorObj Y Z)) q

@[simp] private theorem get_quadLeftPosition (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z) :
    (Tensor.slots shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z).get
        (quadLeftPosition W X Y Z q) = q := by
  exact RealAssociatorLaws.get_slotPosition shiftedReal.D shiftedReal.C
    (tensorObj (tensorObj W X) Y) Z q

@[simp] private theorem get_quadRightPosition (W X Y Z : Obj)
    (q : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))) :
    (Tensor.slots shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))).get
        (quadRightPosition W X Y Z q) = q := by
  exact RealAssociatorLaws.get_slotPosition shiftedReal.D shiftedReal.C
    W (tensorObj X (tensorObj Y Z)) q

private theorem quadPositionLabelEq (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom
      (quadLeftPosition W X Y Z
        (quadLeftSlot W X Y Z i j k l ab abc sourceABCD))).label =
    ((tensorObj W (tensorObj X (tensorObj Y Z))).atom
      (quadRightPosition W X Y Z
        (quadRightSlot W X Y Z i j k l cd bcd targetABCD))).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z
      ((Tensor.slots shiftedReal.D shiftedReal.C
        (tensorObj (tensorObj W X) Y) Z).get _)).label =
    (Tensor.slotAtom shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))
      ((Tensor.slots shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z))).get _)).label
  rw [get_quadLeftPosition, get_quadRightPosition]
  exact quadRouteLabelEq W X Y Z i j k l ab abc sourceABCD
    cd bcd targetABCD

private theorem quadLeftPosition_label (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label) :
    ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom
      (quadLeftPosition W X Y Z
        (quadLeftSlot W X Y Z i j k l ab abc sourceABCD))).label =
      (W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C
    (tensorObj (tensorObj W X) Y) Z
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z).get _)).label = _
  rw [get_quadLeftPosition]
  exact quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD

/-- Unfolding the two matrix compositions expresses one top-route entry as
the same pair of fixed-order `AtomHom` sums used in the support proof. -/
private theorem topRoute_entry_eq_slot_finSum (W X Y Z : Obj)
    (pS : Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size)
    (pT : Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size) :
    topRoute W X Y Z pS pT =
      AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z)).length
        (fun p₂ => AtomHom.comp
          (AtomHom.finSum
            (Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W (tensorObj X Y)) Z).length
            (fun p₁ => AtomHom.comp
              (Tensor.entry shiftedReal.D shiftedReal.C
                (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z)
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj (tensorObj W X) Y) Z).get pS)
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get p₁))
              (RealAssociator.homEntry W (tensorObj X Y) Z
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get p₁)
                ((Tensor.slots shiftedReal.D shiftedReal.C W
                  (tensorObj (tensorObj X Y) Z)).get p₂))))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z)).get p₂)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))) := by
  rfl

/-- Before choosing matrix positions, every unsupported top-route slot
composite is zero already at the `AtomHom` level.  This is the same
fixed-order finite-sum argument used by the existing unitor laws. -/
private theorem topSlotComposite_zero_of_exterior_ne (W X Y Z : Obj)
    (iS : Fin W.size) (jS : Fin X.size) (kS : Fin Y.size) (lS : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom iS).label (X.atom jS).label)
    (abc : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label) (Y.atom kS).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label + (Y.atom kS).label)
      (Z.atom lS).label)
    (iT : Fin W.size) (jT : Fin X.size) (kT : Fin Y.size) (lT : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom kT).label (Z.atom lT).label)
    (bcd : shiftedReal.C.Index (X.atom jT).label
      ((Y.atom kT).label + (Z.atom lT).label))
    (targetABCD : shiftedReal.C.Index (W.atom iT).label
      ((X.atom jT).label + (Y.atom kT).label + (Z.atom lT).label))
    (hpos : iS ≠ iT ∨ jS ≠ jT ∨ kS ≠ kT ∨ lS ≠ lT) :
    let qS := quadLeftSlot W X Y Z
      iS jS kS lS ab abc sourceABCD
    let qT := quadRightSlot W X Y Z
      iT jT kT lT cd bcd targetABCD
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z)).length
        (fun p₂ => AtomHom.comp
          (AtomHom.finSum
            (Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W (tensorObj X Y)) Z).length
            (fun p₁ => AtomHom.comp
              (Tensor.entry shiftedReal.D shiftedReal.C
                (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get p₁))
              (RealAssociator.homEntry W (tensorObj X Y) Z
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get p₁)
                ((Tensor.slots shiftedReal.D shiftedReal.C W
                  (tensorObj (tensorObj X Y) Z)).get p₂))))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z)).get p₂) qT)) =
      AtomHom.zero shiftedReal.D
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z qS)
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W
          (tensorObj X (tensorObj Y Z)) qT) := by
  classical
  dsimp only
  rw [AtomHom.finSum_congr (g := fun _ =>
    AtomHom.zero shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (tensorObj (tensorObj W X) Y) Z
        (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD))
      (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z))
        (quadRightSlot W X Y Z iT jT kT lT cd bcd targetABCD)))]
  · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
  · intro p₂
    rcases exists_eq_topSecondMiddleSlot W X Y Z
        ((Tensor.slots shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z)).get p₂) with
      ⟨i₂, j₂, k₂, l₂, bc₂, bc_d, a_bcd, hq₂⟩
    rw [AtomHom.finSum_comp realComputableShiftedRawDCT.laws.D]
    rw [AtomHom.finSum_congr (g := fun _ =>
      AtomHom.zero shiftedReal.D
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z
          (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD))
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W
          (tensorObj X (tensorObj Y Z))
          (quadRightSlot W X Y Z iT jT kT lT cd bcd targetABCD)))]
    · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
    · intro p₁
      rcases exists_eq_topFirstMiddleSlot W X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (tensorObj W (tensorObj X Y)) Z).get p₁) with
        ⟨i₁, j₁, k₁, l₁, bc₁, a_bc, rowLast, hq₁⟩
      rw [hq₁, hq₂]
      by_cases hi₁ : iS = i₁
      · subst i₁
        by_cases hj₁ : jS = j₁
        · subst j₁
          by_cases hk₁ : kS = k₁
          · subst k₁
            by_cases hl₁ : lS = l₁
            · subst l₁
              by_cases hi₂ : i₂ = iT
              · subst i₂
                by_cases hj₂ : j₂ = jT
                · subst j₂
                  by_cases hk₂ : k₂ = kT
                  · subst k₂
                    by_cases hl₂ : l₂ = lT
                    · subst l₂
                      rcases hpos with hi | hj | hk | hl
                      · simp only [topMiddleEntry_zero_of_first_ne W X Y Z
                          (h := hi),
                          AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                          AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
                      · simp only [topMiddleEntry_zero_of_second_ne W X Y Z
                          (h := hj),
                          AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                          AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
                      · simp only [topMiddleEntry_zero_of_third_ne W X Y Z
                          (h := hk),
                          AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                          AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
                      · simp only [topMiddleEntry_zero_of_fourth_ne W X Y Z
                          (h := hl),
                          AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
                          AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
                    · simp only [topLastEntry_zero_of_fourth_ne W X Y Z
                        (i' := iT) (j' := jT) (k' := kT) (l' := lT)
                        (cd := cd) (bcd := bcd) (targetABCD := targetABCD)
                        (h := hl₂),
                        AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
                  · simp only [topLastEntry_zero_of_third_ne W X Y Z
                      (i' := iT) (j' := jT) (k' := kT) (l' := lT)
                      (cd := cd) (bcd := bcd) (targetABCD := targetABCD)
                      (h := hk₂),
                      AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
                · simp only [topLastEntry_zero_of_middle_ne W X Y Z
                    (i' := iT) (j' := jT) (k' := kT) (l' := lT)
                    (cd := cd) (bcd := bcd) (targetABCD := targetABCD)
                    (h := hj₂),
                    AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
              · simp only [topLastEntry_zero_of_first_ne W X Y Z
                  (i' := iT) (j' := jT) (k' := kT) (l' := lT)
                  (cd := cd) (bcd := bcd) (targetABCD := targetABCD)
                  (h := hi₂),
                  AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
            · simp only [topFirstEntry_zero_of_fourth_ne W X Y Z
                (i := iS) (j := jS) (k := kS) (l := lS)
                (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
                (h := hl₁),
                AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
          · simp only [topFirstEntry_zero_of_third_ne W X Y Z
              (i := iS) (j := jS) (k := kS) (l := lS)
              (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
              (h := hk₁),
              AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        · simp only [topFirstEntry_zero_of_middle_ne W X Y Z
            (i := iS) (j := jS) (k := kS) (l := lS)
            (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
            (h := hj₁),
            AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
      · simp only [topFirstEntry_zero_of_first_ne W X Y Z
          (i := iS) (j := jS) (k := kS) (l := lS)
          (ab := ab) (abc := abc) (sourceABCD := sourceABCD)
          (h := hi₁),
          AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]

/-- Transport the explicit top support theorem to arbitrary endpoint slots.
The endpoint equalities are eliminated before any dependent rewriting of
`AtomHom` is attempted. -/
private theorem topSlotComposite_zero_of_eq_explicit (W X Y Z : Obj)
    (iS : Fin W.size) (jS : Fin X.size) (kS : Fin Y.size) (lS : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom iS).label (X.atom jS).label)
    (abc : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label) (Y.atom kS).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label + (Y.atom kS).label)
      (Z.atom lS).label)
    (iT : Fin W.size) (jT : Fin X.size) (kT : Fin Y.size) (lT : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom kT).label (Z.atom lT).label)
    (bcd : shiftedReal.C.Index (X.atom jT).label
      ((Y.atom kT).label + (Z.atom lT).label))
    (targetABCD : shiftedReal.C.Index (W.atom iT).label
      ((X.atom jT).label + (Y.atom kT).label + (Z.atom lT).label))
    {qS : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z}
    {qT : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))}
    (hqS : qS = quadLeftSlot W X Y Z
      iS jS kS lS ab abc sourceABCD)
    (hqT : qT = quadRightSlot W X Y Z
      iT jT kT lT cd bcd targetABCD)
    (hpos : iS ≠ iT ∨ jS ≠ jT ∨ kS ≠ kT ∨ lS ≠ lT) :
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C W
          (tensorObj (tensorObj X Y) Z)).length
        (fun p₂ => AtomHom.comp
          (AtomHom.finSum
            (Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W (tensorObj X Y)) Z).length
            (fun p₁ => AtomHom.comp
              (Tensor.entry shiftedReal.D shiftedReal.C
                (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get p₁))
              (RealAssociator.homEntry W (tensorObj X Y) Z
                ((Tensor.slots shiftedReal.D shiftedReal.C
                  (tensorObj W (tensorObj X Y)) Z).get p₁)
                ((Tensor.slots shiftedReal.D shiftedReal.C W
                  (tensorObj (tensorObj X Y) Z)).get p₂))))
          (Tensor.entry shiftedReal.D shiftedReal.C
            (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z)).get p₂) qT)) =
      AtomHom.zero shiftedReal.D
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z qS)
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W
          (tensorObj X (tensorObj Y Z)) qT) := by
  subst qS
  subst qT
  exact topSlotComposite_zero_of_exterior_ne W X Y Z
    iS jS kS lS ab abc sourceABCD
    iT jT kT lT cd bcd targetABCD hpos

/-- A top-route entry vanishes when its source and target four-object
positions differ.  The proof uses only the support of its three edges. -/
private theorem topRoute_entry_zero_of_exterior_ne (W X Y Z : Obj)
    (iS : Fin W.size) (jS : Fin X.size) (kS : Fin Y.size) (lS : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom iS).label (X.atom jS).label)
    (abc : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label) (Y.atom kS).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label + (Y.atom kS).label)
      (Z.atom lS).label)
    (iT : Fin W.size) (jT : Fin X.size) (kT : Fin Y.size) (lT : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom kT).label (Z.atom lT).label)
    (bcd : shiftedReal.C.Index (X.atom jT).label
      ((Y.atom kT).label + (Z.atom lT).label))
    (targetABCD : shiftedReal.C.Index (W.atom iT).label
      ((X.atom jT).label + (Y.atom kT).label + (Z.atom lT).label))
    (hpos : iS ≠ iT ∨ jS ≠ jT ∨ kS ≠ kT ∨ lS ≠ lT) :
    let qS := quadLeftSlot W X Y Z
      iS jS kS lS ab abc sourceABCD
    let qT := quadRightSlot W X Y Z
      iT jT kT lT cd bcd targetABCD
    topRoute W X Y Z (quadLeftPosition W X Y Z qS)
        (quadRightPosition W X Y Z qT) =
      AtomHom.zero shiftedReal.D _ _ := by
  classical
  dsimp only
  rw [topRoute_entry_eq_slot_finSum]
  apply topSlotComposite_zero_of_eq_explicit W X Y Z
    iS jS kS lS ab abc sourceABCD
    iT jT kT lT cd bcd targetABCD (hpos := hpos)
  · exact get_quadLeftPosition W X Y Z _
  · exact get_quadRightPosition W X Y Z _

/-- Unfolding the bottom matrix composition leaves one fixed-order sum over
the common middle object `(W ⊗ X) ⊗ (Y ⊗ Z)`. -/
private theorem bottomRoute_entry_eq_slot_finSum (W X Y Z : Obj)
    (pS : Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size)
    (pT : Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size) :
    bottomRoute W X Y Z pS pT =
      AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z)).length
        (fun pM => AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj (tensorObj W X) Y) Z).get pS)
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W X) (tensorObj Y Z)).get pM))
          (RealAssociator.homEntry W X (tensorObj Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W X) (tensorObj Y Z)).get pM)
            ((Tensor.slots shiftedReal.D shiftedReal.C W
              (tensorObj X (tensorObj Y Z))).get pT))) := by
  rfl

/-- Before choosing matrix positions, every unsupported bottom-route slot
composite is zero by the two existing ternary associator support lemmas. -/
private theorem bottomSlotComposite_zero_of_exterior_ne (W X Y Z : Obj)
    (iS : Fin W.size) (jS : Fin X.size) (kS : Fin Y.size) (lS : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom iS).label (X.atom jS).label)
    (abc : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label) (Y.atom kS).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label + (Y.atom kS).label)
      (Z.atom lS).label)
    (iT : Fin W.size) (jT : Fin X.size) (kT : Fin Y.size) (lT : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom kT).label (Z.atom lT).label)
    (bcd : shiftedReal.C.Index (X.atom jT).label
      ((Y.atom kT).label + (Z.atom lT).label))
    (targetABCD : shiftedReal.C.Index (W.atom iT).label
      ((X.atom jT).label + (Y.atom kT).label + (Z.atom lT).label))
    (hpos : iS ≠ iT ∨ jS ≠ jT ∨ kS ≠ kT ∨ lS ≠ lT) :
    let qS := quadLeftSlot W X Y Z
      iS jS kS lS ab abc sourceABCD
    let qT := quadRightSlot W X Y Z
      iT jT kT lT cd bcd targetABCD
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z)).length
        (fun pM => AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W X) (tensorObj Y Z)).get pM))
          (RealAssociator.homEntry W X (tensorObj Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W X) (tensorObj Y Z)).get pM) qT)) =
      AtomHom.zero shiftedReal.D
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z qS)
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W
          (tensorObj X (tensorObj Y Z)) qT) := by
  classical
  dsimp only
  let pAB := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    W X (binarySlot W X iS jS ab)
  let pCD := RealAssociatorLaws.slotPosition shiftedReal.D shiftedReal.C
    Y Z (binarySlot Y Z kT lT cd)
  rw [AtomHom.finSum_congr (g := fun _ =>
    AtomHom.zero shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (tensorObj (tensorObj W X) Y) Z
        (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD))
      (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z))
        (quadRightSlot W X Y Z iT jT kT lT cd bcd targetABCD)))]
  · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
  · intro pM
    generalize hqM : (Tensor.slots shiftedReal.D shiftedReal.C
      (tensorObj W X) (tensorObj Y Z)).get pM = qM
    change AtomHom.comp
        (RealAssociator.homEntry (tensorObj W X) Y Z
          (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD) qM)
        (RealAssociator.homEntry W X (tensorObj Y Z) qM
          (quadRightSlot W X Y Z
            iT jT kT lT cd bcd targetABCD)) = _
    by_cases hAB : qM.left = pAB
    · by_cases hCD : qM.right = pCD
      · rcases hpos with hi | hj | hk | hl
        · have hSupport :
              ((Tensor.slots shiftedReal.D shiftedReal.C W X).get
                  qM.left).left ≠
                (quadRightSlot W X Y Z
                  iT jT kT lT cd bcd targetABCD).left := by
              intro hEq
              apply hi
              rw [hAB] at hEq
              dsimp only [pAB] at hEq
              rw [RealAssociatorLaws.get_slotPosition,
                quadRightSlot_left, binarySlot, Tensor.Slot.left] at hEq
              exact hEq
          have hz := RealAssociatorNaturality.realHomEntry_zero_of_left_ne
            W X (tensorObj Y Z) qM
            (quadRightSlot W X Y Z iT jT kT lT cd bcd targetABCD)
            hSupport
          simpa only [hz,
            AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
        · have hSupport :
              ((Tensor.slots shiftedReal.D shiftedReal.C W X).get
                  qM.left).right ≠
                ((Tensor.slots shiftedReal.D shiftedReal.C X
                  (tensorObj Y Z)).get
                    (quadRightSlot W X Y Z
                      iT jT kT lT cd bcd targetABCD).right).left := by
              intro hEq
              apply hj
              rw [hAB] at hEq
              dsimp only [pAB] at hEq
              rw [RealAssociatorLaws.get_slotPosition,
                quadRightSlot_inner, RealAssociatorLaws.rightRouteSlot_left,
                binarySlot, Tensor.Slot.right] at hEq
              exact hEq
          have hz := RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
            W X (tensorObj Y Z) qM
            (quadRightSlot W X Y Z iT jT kT lT cd bcd targetABCD)
            hSupport
          simpa only [hz,
            AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
        · have hSupport :
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (tensorObj W X) Y).get
                  (quadLeftSlot W X Y Z
                    iS jS kS lS ab abc sourceABCD).left).right ≠
                ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                  qM.right).left := by
              intro hEq
              apply hk
              rw [hCD] at hEq
              dsimp only [pCD] at hEq
              rw [quadLeftSlot_inner,
                RealAssociatorLaws.leftRouteSlot_right,
                RealAssociatorLaws.get_slotPosition, binarySlot,
                Tensor.Slot.left] at hEq
              exact hEq
          have hz := RealAssociatorNaturality.realHomEntry_zero_of_middle_ne
            (tensorObj W X) Y Z
            (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD) qM
            hSupport
          simpa only [hz,
            AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        · have hSupport :
              (quadLeftSlot W X Y Z
                  iS jS kS lS ab abc sourceABCD).right ≠
                ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                  qM.right).right := by
              intro hEq
              apply hl
              rw [hCD] at hEq
              dsimp only [pCD] at hEq
              rw [quadLeftSlot_right,
                RealAssociatorLaws.get_slotPosition, binarySlot,
                Tensor.Slot.right] at hEq
              exact hEq
          have hz := RealAssociatorNaturality.realHomEntry_zero_of_right_ne
            (tensorObj W X) Y Z
            (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD) qM
            hSupport
          simpa only [hz,
            AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
      · have hSupport : qM.right ≠
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (tensorObj Y Z)).get
                (quadRightSlot W X Y Z
                  iT jT kT lT cd bcd targetABCD).right).right := by
            rw [quadRightSlot_lastPosition W X Y Z
              iT jT kT lT cd bcd targetABCD]
            exact hCD
        have hz := RealAssociatorNaturality.realHomEntry_zero_of_right_ne
          W X (tensorObj Y Z) qM
          (quadRightSlot W X Y Z iT jT kT lT cd bcd targetABCD)
          hSupport
        simpa only [hz,
          AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    · have hSupport :
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (tensorObj W X) Y).get
              (quadLeftSlot W X Y Z
                iS jS kS lS ab abc sourceABCD).left).left ≠ qM.left := by
          rw [quadLeftSlot_firstPosition W X Y Z
            iS jS kS lS ab abc sourceABCD]
          exact Ne.symm hAB
      have hz := RealAssociatorNaturality.realHomEntry_zero_of_left_ne
        (tensorObj W X) Y Z
        (quadLeftSlot W X Y Z iS jS kS lS ab abc sourceABCD) qM
        hSupport
      simpa only [hz,
        AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]

/-- Transport the explicit bottom support theorem to arbitrary endpoint
slots by eliminating the endpoint equalities first. -/
private theorem bottomSlotComposite_zero_of_eq_explicit (W X Y Z : Obj)
    (iS : Fin W.size) (jS : Fin X.size) (kS : Fin Y.size) (lS : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom iS).label (X.atom jS).label)
    (abc : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label) (Y.atom kS).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label + (Y.atom kS).label)
      (Z.atom lS).label)
    (iT : Fin W.size) (jT : Fin X.size) (kT : Fin Y.size) (lT : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom kT).label (Z.atom lT).label)
    (bcd : shiftedReal.C.Index (X.atom jT).label
      ((Y.atom kT).label + (Z.atom lT).label))
    (targetABCD : shiftedReal.C.Index (W.atom iT).label
      ((X.atom jT).label + (Y.atom kT).label + (Z.atom lT).label))
    {qS : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z}
    {qT : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))}
    (hqS : qS = quadLeftSlot W X Y Z
      iS jS kS lS ab abc sourceABCD)
    (hqT : qT = quadRightSlot W X Y Z
      iT jT kT lT cd bcd targetABCD)
    (hpos : iS ≠ iT ∨ jS ≠ jT ∨ kS ≠ kT ∨ lS ≠ lT) :
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C
          (tensorObj W X) (tensorObj Y Z)).length
        (fun pM => AtomHom.comp
          (RealAssociator.homEntry (tensorObj W X) Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W X) (tensorObj Y Z)).get pM))
          (RealAssociator.homEntry W X (tensorObj Y Z)
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (tensorObj W X) (tensorObj Y Z)).get pM) qT)) =
      AtomHom.zero shiftedReal.D
        (Tensor.slotAtom shiftedReal.D shiftedReal.C
          (tensorObj (tensorObj W X) Y) Z qS)
        (Tensor.slotAtom shiftedReal.D shiftedReal.C W
          (tensorObj X (tensorObj Y Z)) qT) := by
  subst qS
  subst qT
  exact bottomSlotComposite_zero_of_exterior_ne W X Y Z
    iS jS kS lS ab abc sourceABCD
    iT jT kT lT cd bcd targetABCD hpos

/-- A bottom-route entry vanishes when its source and target four-object
positions differ.  The two middle-slot positions are first compared with
the source `W ⊗ X` block and target `Y ⊗ Z` block; once both agree, one
of the four ternary associator support conditions detects the mismatch. -/
private theorem bottomRoute_entry_zero_of_exterior_ne (W X Y Z : Obj)
    (iS : Fin W.size) (jS : Fin X.size) (kS : Fin Y.size) (lS : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom iS).label (X.atom jS).label)
    (abc : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label) (Y.atom kS).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom iS).label + (X.atom jS).label + (Y.atom kS).label)
      (Z.atom lS).label)
    (iT : Fin W.size) (jT : Fin X.size) (kT : Fin Y.size) (lT : Fin Z.size)
    (cd : shiftedReal.C.Index (Y.atom kT).label (Z.atom lT).label)
    (bcd : shiftedReal.C.Index (X.atom jT).label
      ((Y.atom kT).label + (Z.atom lT).label))
    (targetABCD : shiftedReal.C.Index (W.atom iT).label
      ((X.atom jT).label + (Y.atom kT).label + (Z.atom lT).label))
    (hpos : iS ≠ iT ∨ jS ≠ jT ∨ kS ≠ kT ∨ lS ≠ lT) :
    let qS := quadLeftSlot W X Y Z
      iS jS kS lS ab abc sourceABCD
    let qT := quadRightSlot W X Y Z
      iT jT kT lT cd bcd targetABCD
    bottomRoute W X Y Z (quadLeftPosition W X Y Z qS)
        (quadRightPosition W X Y Z qT) =
      AtomHom.zero shiftedReal.D _ _ := by
  classical
  dsimp only
  rw [bottomRoute_entry_eq_slot_finSum]
  apply bottomSlotComposite_zero_of_eq_explicit W X Y Z
    iS jS kS lS ab abc sourceABCD
    iT jT kT lT cd bcd targetABCD (hpos := hpos)
  · exact get_quadLeftPosition W X Y Z _
  · exact get_quadRightPosition W X Y Z _

/-! ### Transport of route expansions to explicit endpoint slots -/

/-- Cast the bottom-route expansion to a common total label before replacing
the enumerated endpoint slots by explicit ones.  The common carrier is
essential: the coefficient carrier depends on the endpoint labels, so the
slot equalities cannot be rewritten directly inside an uncast coefficient. -/
private theorem cast_bottom_coeff_as_explicit_slot_sum (W X Y Z : Obj)
    (pS : Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size)
    (pT : Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size)
    (qS : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z)
    (qT : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)))
    (hqS : (Tensor.slots shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z).get pS = qS)
    (hqT : (Tensor.slots shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))).get pT = qT)
    (t : ZMod 8)
    (hPos : ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label = t)
    (hExp : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z qS).label = t)
    (hST : ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label =
      ((tensorObj W (tensorObj X (tensorObj Y Z))).atom pT).label)
    (hSlot : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z qS).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z)) qT).label) :
    cast (congrArg
      (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hPos)
        ((bottomRoute W X Y Z pS pT).coeff hST) =
      cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hExp)
        (∑ qM : Tensor.Slot shiftedReal.D shiftedReal.C
            (tensorObj W X) (tensorObj Y Z),
          (AtomHom.comp
            (RealAssociator.homEntry (tensorObj W X) Y Z qS qM)
            (RealAssociator.homEntry W X (tensorObj Y Z) qM qT)).coeff
              hSlot) := by
  rw [bottom_coeff_as_slot_sum W X Y Z pS pT hST]
  cases hqS
  cases hqT
  have hp : hPos = hExp := Subsingleton.elim _ _
  have hp' : hST = hSlot := Subsingleton.elim _ _
  cases hp
  cases hp'
  rfl

/-- The analogous common-carrier transport for the top route, whose expansion
has two intermediate slot sums. -/
private theorem cast_top_coeff_as_explicit_slot_sum (W X Y Z : Obj)
    (pS : Fin (tensorObj (tensorObj (tensorObj W X) Y) Z).size)
    (pT : Fin (tensorObj W (tensorObj X (tensorObj Y Z))).size)
    (qS : Tensor.Slot shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z)
    (qT : Tensor.Slot shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z)))
    (hqS : (Tensor.slots shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z).get pS = qS)
    (hqT : (Tensor.slots shiftedReal.D shiftedReal.C W
      (tensorObj X (tensorObj Y Z))).get pT = qT)
    (t : ZMod 8)
    (hPos : ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label = t)
    (hExp : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z qS).label = t)
    (hST : ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label =
      ((tensorObj W (tensorObj X (tensorObj Y Z))).atom pT).label)
    (hSlot : (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z qS).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C W
        (tensorObj X (tensorObj Y Z)) qT).label) :
    cast (congrArg
      (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hPos)
        ((topRoute W X Y Z pS pT).coeff hST) =
      cast (congrArg
        (fun a : ZMod 8 => (shiftedReal.D.algebra a).carrier) hExp)
        (∑ q₁ : Tensor.Slot shiftedReal.D shiftedReal.C
            (tensorObj W (tensorObj X Y)) Z,
          ∑ q₂ : Tensor.Slot shiftedReal.D shiftedReal.C W
              (tensorObj (tensorObj X Y) Z),
            (AtomHom.comp
              (AtomHom.comp
                (Tensor.entry shiftedReal.D shiftedReal.C
                  (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z) qS q₁)
                (RealAssociator.homEntry W (tensorObj X Y) Z q₁ q₂))
              (Tensor.entry shiftedReal.D shiftedReal.C
                (Hom.id shiftedReal.D W) (RealAssociator.hom X Y Z) q₂ qT)).coeff
                  hSlot) := by
  rw [top_coeff_as_slot_sum W X Y Z pS pT hST]
  cases hqS
  cases hqT
  have hp : hPos = hExp := Subsingleton.elim _ _
  have hp' : hST = hSlot := Subsingleton.elim _ _
  cases hp
  cases hp'
  rfl

/-! ### Common scalar surrounding the saved fourfold kernels -/

private def topCommonSign (a b c d : ZMod 8)
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD : ZMod 2) : ℝ :=
  RawDCT.paritySign
      (topCoordinateExponent sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD
        (shiftNu realComputableNuBeta.data a b)
        (shiftNu realComputableNuBeta.data b c)
        (shiftNu realComputableNuBeta.data c d)
        (shiftNu realComputableNuBeta.data (a + b) c)
        (shiftNu realComputableNuBeta.data a (b + c))
        (shiftNu realComputableNuBeta.data (a + b + c) d)
        (shiftNu realComputableNuBeta.data (b + c) d)
        (shiftNu realComputableNuBeta.data b (c + d))
        (shiftNu realComputableNuBeta.data (a + b) (c + d))
        (shiftNu realComputableNuBeta.data a (b + c + d))
        (rawReal.T.parity a b c) (rawReal.T.parity b c d)) *
    (RawDCT.paritySign
        (shiftPentagonTopDegree rawReal realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
      RawDCT.paritySign (rawReal.T.parity a (b + c) d * pBC))

private def bottomCommonSign (a b c d : ZMod 8)
    (sY sZ pAB pABC pCD pBCD : ZMod 2) : ℝ :=
  RawDCT.paritySign
      (bottomCoordinateExponent sY sZ pAB pABC pCD pBCD
        (shiftNu realComputableNuBeta.data a b)
        (shiftNu realComputableNuBeta.data c d)
        (shiftNu realComputableNuBeta.data (a + b) c)
        (shiftNu realComputableNuBeta.data (a + b + c) d)
        (shiftNu realComputableNuBeta.data (a + b) (c + d))
        (shiftNu realComputableNuBeta.data a (b + c + d))) *
    (RawDCT.paritySign
        (shiftPentagonBottomDegree realComputableNuBeta.data
          (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
          (Multiplicative.ofAdd c) (Multiplicative.ofAdd d)) *
      (RawDCT.paritySign (rawReal.T.parity (a + b) c d * pAB) *
        RawDCT.paritySign
          (pCD * (rawReal.T.parity a b (c + d) + pAB))))

private theorem topCommonSign_eq_bottomCommonSign (a b c d : ZMod 8)
    (sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD : ZMod 2) :
    topCommonSign a b c d sY sZ pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD =
      bottomCommonSign a b c d sY sZ pAB pABC pCD pBCD := by
  exact realCoordinateCommonSign_eq a b c d sY sZ
    pAB pABC pBC pA_BC pBC_D pA_BCD pCD pBCD

/-! ### Route coefficients versus the saved executable kernel -/

/-- Coefficient form of the two-edge route.  This is the finite-coordinate
counterpart of `RealPChiRouteBottom.semanticObserve_famBot`: the proof only
reindexes the middle slot and expands one coefficient-algebra product in its
canonical basis. -/
private theorem bottomCompositeEntry_eq_scalarCoordinate (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label))) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    let pS := quadLeftPosition W X Y Z qS
    let pT := quadRightPosition W X Y Z qT
    let hS := quadLeftPosition_label W X Y Z
      i j k l ab abc sourceABCD
    let hST := quadPositionLabelEq W X Y Z i j k l
      ab abc sourceABCD cd bcd targetABCD
    (observeCoefficient
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label)
      (cast (congrArg
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) hS)
        ((bottomRoute W X Y Z pS pT).coeff hST)))
      (coefficientIndex
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label) basis) =
      bottomCommonSign
          (W.atom i).label (X.atom j).label (Y.atom k).label (Z.atom l).label
          (Y.atom k).shift (Z.atom l).shift
          (rawRowParityOfShifted (W.atom i).label (X.atom j).label ab)
          (rawRowParityOfShifted
            ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc)
          (rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd)
          (rawRowParityOfShifted (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label) bcd) *
        ((shiftPentagonBottomScalar realComputableNuBeta.data
            (Multiplicative.ofAdd (W.atom i).label)
            (Multiplicative.ofAdd (X.atom j).label)
            (Multiplicative.ofAdd (Y.atom k).label)
            (Multiplicative.ofAdd (Z.atom l).label) : ℝ) *
          ((RawDCT.RealPChiKernel.botCoeff
            (W.atom i).label (X.atom j).label
            (Y.atom k).label (Z.atom l).label
            (quadSource i j k l ab abc sourceABCD)
            (quadTarget i j k l cd bcd targetABCD basis) : ℤ) : ℝ)) := by
  classical
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let pS := quadLeftPosition W X Y Z qS
  let pT := quadRightPosition W X Y Z qT
  let hS := quadLeftPosition_label W X Y Z i j k l ab abc sourceABCD
  let hExp := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
  let hST := quadPositionLabelEq W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
  let hSlot := quadRouteLabelEq W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
  change (observeCoefficient
    ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label)
    (cast (congrArg
      (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hS)
      ((bottomRoute W X Y Z pS pT).coeff hST)))
        (coefficientIndex
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label) basis) = _
  have hSlots' := cast_bottom_coeff_as_explicit_slot_sum W X Y Z
    pS pT qS qT
    (by simpa only [pS] using get_quadLeftPosition W X Y Z qS)
    (by simpa only [pT] using get_quadRightPosition W X Y Z qT)
    ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label) hS hExp hST hSlot
  rw [bottom_quad_slot_sum_eq_row_sum W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD (hSlot := hSlot)] at hSlots'
  rw [cast_algebra_sum_of_label_eq hExp] at hSlots'
  simp_rw [cast_bottom_comp_coeff_at_total W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD] at hSlots'
  simp_rw [cast_bottomSecondHomEntry_at_total,
    cast_bottomFirstHomEntry_at_total] at hSlots'
  have hObserved := congrArg
    (observeCoefficient
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label)) hSlots'
  rw [observeCoefficient_sum] at hObserved
  have hSlotsBasis := congrArg
    (fun u : RModCoordinate.Coeff
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label) => u
          (coefficientIndex
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
              (Z.atom l).label) basis)) hObserved
  rw [hSlotsBasis]
  rw [Finset.sum_apply]
  simp_rw [observed_coefficient_mul_expand_right]
  simp_rw [RModCoordinate.Coeff.mul_smul_right]
  simp_rw [Finset.sum_apply]
  simp_rw [observeCoefficient_smul]
  simp_rw [RModCoordinate.Coeff.smul]
  unfold bottomCommonSign
  rw [coe_shiftPentagonBottomScalar]
  simp_rw [shiftedRowParity_eq]
  simp only [RawDCT.RealPChiKernel.botCoeff]
  simp_rw [sumRange_eq_sumShiftedIndex, sumRange_eq_sumNativeBasis]
  push_cast
  repeat' rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rowABCD _
  repeat' rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro basis4 _
  rw [observed_cast_algebra_mul_basis_apply]
  rw [observeCoefficient_smul]
  rw [RModCoordinate.Coeff.smul_mul]
  rw [RModCoordinate.Coeff.smul_apply]
  rw [observed_realShiftedHomCoefficient_apply_eq]
  rw [observed_realShiftedHomCoefficient_mul_basis_eq]
  rw [realShiftedHomCoefficient_apply_public]
  rw [realShiftedHomCoefficient_mul_basis_public]
  rotate_left
  simp only [add_assoc]
  have hABNat : RawDCT.RealPChiKernel.rowParityNat
      (W.atom i).label (X.atom j).label
        (quadSource i j k l ab abc sourceABCD).1.1.val =
      (rawRowParityOfShifted
        (W.atom i).label (X.atom j).label ab).val := by
    change RawDCT.RealPChiKernel.rowParityNat
      (W.atom i).label (X.atom j).label ab.val = _
    exact rowParityNat_eq_rawRowParityOfShifted_val _ _ ab
  have hCDNat : RawDCT.RealPChiKernel.rowParityNat
      (Y.atom k).label (Z.atom l).label
        (quadTarget i j k l cd bcd targetABCD basis).1.1.val =
      (rawRowParityOfShifted
        (Y.atom k).label (Z.atom l).label cd).val := by
    change RawDCT.RealPChiKernel.rowParityNat
      (Y.atom k).label (Z.atom l).label cd.val = _
    exact rowParityNat_eq_rawRowParityOfShifted_val _ _ cd
  rw [hABNat, hCDNat]
  simp_rw [connectorParityNat_eq_rawParity_val]
  simp_rw [cast_bottomKoszulSigns_eq_paritySigns]
  have hTargetBasisVal :
      (quadTarget i j k l cd bcd targetABCD basis).2.2.val = basis.val := by
    unfold quadTarget
    exact coefficientBasis_cast_val
      (quadTotalAssoc (W.atom i).label (X.atom j).label
        (Y.atom k).label (Z.atom l).label) basis
  rw [hTargetBasisVal]
  simp only [quadSource, quadTarget, castIndex_val]
  unfold leftRouteFrameSign rightRouteFrameSign
  simp only [finCongr_symm_val, coefficientIndex_val, kernelIndex_val]
  unfold rawRowParityOfShifted
  rw [← bottomCoordinateParityProduct_eq]
  by_cases hzero : RawDCT.RealPChiKernel.connectorLinearCoeff
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label (Z.atom l).label
      cd.val rowABCD.val abc.val sourceABCD.val basis4.val
      (RawDCT.RealPChiKernel.coefficientUnitIndex
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label)).val = 0
  · simp [hzero]
  · simp only [hzero, if_false]
    simp only [Units.val_inv_eq_inv_val]
    ring_nf
    simp only [paritySign_sq]
    ring

set_option maxHeartbeats 3200000 in
/-- Coefficient form of the three-edge route.  This is the corresponding
finite-coordinate adapter for `RealPChiRouteTop.semanticObserve_famTop`.
The two intermediate tensor-slot sums are reindexed by
`topFirstMiddleSlot` and `topSecondMiddleSlot`; the coefficient-algebra
products are then expanded in the same canonical bases as `topCoeff`. -/
private theorem topCompositeEntry_eq_scalarCoordinate (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label))
    (basis : Fin (RawDCT.RealPChiKernel.coefficientRank
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label))) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    let pS := quadLeftPosition W X Y Z qS
    let pT := quadRightPosition W X Y Z qT
    let hS := quadLeftPosition_label W X Y Z
      i j k l ab abc sourceABCD
    let hST := quadPositionLabelEq W X Y Z i j k l
      ab abc sourceABCD cd bcd targetABCD
    (observeCoefficient
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label)
      (cast (congrArg
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) hS)
        ((topRoute W X Y Z pS pT).coeff hST)))
      (coefficientIndex
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label) basis) =
      bottomCommonSign
          (W.atom i).label (X.atom j).label (Y.atom k).label (Z.atom l).label
          (Y.atom k).shift (Z.atom l).shift
          (rawRowParityOfShifted (W.atom i).label (X.atom j).label ab)
          (rawRowParityOfShifted
            ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc)
          (rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd)
          (rawRowParityOfShifted (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label) bcd) *
        ((shiftPentagonTopScalar rawReal realComputableNuBeta.data
            (Multiplicative.ofAdd (W.atom i).label)
            (Multiplicative.ofAdd (X.atom j).label)
            (Multiplicative.ofAdd (Y.atom k).label)
            (Multiplicative.ofAdd (Z.atom l).label) : ℝ) *
          ((RawDCT.RealPChiKernel.topCoeff
            (W.atom i).label (X.atom j).label
            (Y.atom k).label (Z.atom l).label
            (quadSource i j k l ab abc sourceABCD)
            (quadTarget i j k l cd bcd targetABCD basis) : ℤ) : ℝ)) := by
  classical
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let pS := quadLeftPosition W X Y Z qS
  let pT := quadRightPosition W X Y Z qT
  let hS := quadLeftPosition_label W X Y Z i j k l ab abc sourceABCD
  let hExp := quadLeftSlot_label W X Y Z i j k l ab abc sourceABCD
  let hST := quadPositionLabelEq W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
  let hSlot := quadRouteLabelEq W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
  change (observeCoefficient
    ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label)
    (cast (congrArg
      (fun q : ZMod 8 => (shiftedReal.D.algebra q).carrier) hS)
      ((topRoute W X Y Z pS pT).coeff hST)))
        (coefficientIndex
          ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
            (Z.atom l).label) basis) = _
  letI : Fact (SuperAlgebraLaws
      (shiftedReal.D.algebra
        ((tensorObj (tensorObj (tensorObj W X) Y) Z).atom pS).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  have hSlots' := cast_top_coeff_as_explicit_slot_sum W X Y Z
    pS pT qS qT
    (by simpa only [pS] using get_quadLeftPosition W X Y Z qS)
    (by simpa only [pT] using get_quadRightPosition W X Y Z qT)
    ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label) hS hExp hST hSlot
  rw [top_quad_slot_sum_eq_row_sum W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD (hSlot := hSlot)] at hSlots'
  simp_rw [cast_algebra_sum_of_label_eq hExp] at hSlots'
  simp_rw [cast_top_triple_comp_coeff_at_total W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD] at hSlots'
  simp_rw [cast_topFinalTensorEntry_at_total,
    cast_topMiddleHomEntry_at_total,
    cast_topFirstTensorEntry_at_total] at hSlots'
  have hObserved := congrArg
    (observeCoefficient
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label)) hSlots'
  rw [observeCoefficient_sum] at hObserved
  have hSlotsBasis := congrArg
    (fun u : RModCoordinate.Coeff
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
        (Z.atom l).label) => u
          (coefficientIndex
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
              (Z.atom l).label) basis)) hObserved
  rw [hSlotsBasis]
  rw [Finset.sum_apply]
  simp_rw [observed_four_sum_triple_expand_first]
  simp_rw [coefficient_triple_expand_middle_kernel]
  repeat' rw [Finset.sum_apply]
  simp_rw [RModCoordinate.Coeff.mul_smul_right]
  simp_rw [RModCoordinate.Coeff.smul]
  simp_rw [observeCoefficient_smul]
  simp_rw [RModCoordinate.Coeff.smul_apply]
  simp_rw [observed_leftWhisker_apply]
  simp_rw [observed_topMiddle_mul_basis]
  simp_rw [Finset.sum_apply]
  simp_rw [RModCoordinate.Coeff.smul_apply]
  simp_rw [observed_topFinal_mul_basis]
  simp_rw [observed_realShiftedHomCoefficient_apply_eq]
  simp_rw [realShiftedHomCoefficient_apply_public]
  rw [RawDCT.RealPChiRouteTop.topCoeff_eq_unguarded]
  push_cast
  rw [coe_shiftPentagonTopScalar]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3, 2, v4, 2, v5, 2, v6, 2, v7]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3, 2, v4, 2, v5, 2, v6]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3, 2, v4, 2, v5]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3, 2, v4]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3, 2, v4, 2, v5]
    rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, v1, 2, v2, 2, v3, 2, v4]
    rw [Finset.sum_comm]
  repeat' rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rowBC _
  apply Finset.sum_congr rfl
  intro rowA_BC _
  apply Finset.sum_congr rfl
  intro basis1 _
  apply Finset.sum_congr rfl
  intro rowLast1 _
  apply Finset.sum_congr rfl
  intro basis2 _
  apply Finset.sum_congr rfl
  intro rowBC_D _
  apply Finset.sum_congr rfl
  intro rowA_BCD _
  apply Finset.sum_congr rfl
  intro basis3 _
  apply Finset.sum_congr rfl
  intro basis4 _
  unfold leftRouteFrameSign rightRouteFrameSign
  simp_rw [shiftedRowParity_eq]
  try simp_rw [connectorParityNat_eq_rawParity_val]
  try simp_rw [rowParityNat_eq_rawRowParityOfShifted_val]
  try simp_rw [cast_koszulSign_eq_paritySign]
  unfold bottomCommonSign
  simp only [← _root_.add_assoc]
  have hfold : ∀ (x y : ZMod 8) (r : shiftedReal.C.Index x y),
      rawReal.C.rowParity x y (rawIndexOfShifted x y r) =
        rawRowParityOfShifted x y r := fun _ _ _ => rfl
  have hunit : ∀ t : ZMod 8,
      ((RawDCT.RealPChiKernel.coefficientUnitIndex t :
        Fin (RawDCT.RealPChiKernel.coefficientRank t)) : ℕ) = 0 :=
    fun _ => rfl
  have hci : ∀ (t : ZMod 8)
      (b : Fin (RawDCT.RealPChiKernel.coefficientRank t)),
      ((coefficientIndex t b : Fin (realRepDim t.val)) : ℕ) = b.val :=
    fun _ _ => rfl
  simp only [hfold, Units.val_inv_eq_inv_val, quadSource, quadTarget,
    hunit, hci,
    coefficientBasis_cast_val (quadTotalAssoc (W.atom i).label
      (X.atom j).label (Y.atom k).label (Z.atom l).label)]
  exact topSummand_eq_bottomSummand
    (W.atom i).label (X.atom j).label (Y.atom k).label (Z.atom l).label
    (Y.atom k).shift (Z.atom l).shift
    (rawRowParityOfShifted (W.atom i).label (X.atom j).label ab)
    (rawRowParityOfShifted
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc)
    (rawRowParityOfShifted (X.atom j).label (Y.atom k).label rowBC)
    (rawRowParityOfShifted (W.atom i).label
      ((X.atom j).label + (Y.atom k).label) rowA_BC)
    (rawRowParityOfShifted
      ((X.atom j).label + (Y.atom k).label) (Z.atom l).label rowBC_D)
    (rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd)
    (rawRowParityOfShifted (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label) bcd)
    ((RawDCT.RealPChiKernel.connectorLinearCoeff
      (W.atom i).label (X.atom j).label (Y.atom k).label
      rowBC.val rowA_BC.val ab.val abc.val basis1.val 0
      : ℤ) : ℝ)
    ((RawDCT.RealPChiKernel.fusionLeftSlotCoeff
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label basis1.val rowLast1.val basis2.val
      sourceABCD.val 0 : ℤ) : ℝ)
    ((RawDCT.RealPChiKernel.connectorLinearCoeff
      (W.atom i).label ((X.atom j).label + (Y.atom k).label)
      (Z.atom l).label rowBC_D.val rowA_BCD.val rowA_BC.val
      rowLast1.val basis3.val basis2.val : ℤ) : ℝ)
    ((RawDCT.RealPChiKernel.connectorLinearCoeff
      (X.atom j).label (Y.atom k).label (Z.atom l).label
      cd.val bcd.val rowBC.val rowBC_D.val basis4.val 0
      : ℤ) : ℝ)
    ((RawDCT.RealPChiKernel.fusionRightSlotCoeff
      (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)
      basis4.val targetABCD.val basis.val
      rowA_BCD.val basis3.val : ℤ) : ℝ)

/-! ### Insertion of the already certified scalar-coordinate pentagon -/

private theorem explicitQuadEntry_eq (W X Y Z : Obj)
    (i : Fin W.size) (j : Fin X.size) (k : Fin Y.size) (l : Fin Z.size)
    (ab : shiftedReal.C.Index (W.atom i).label (X.atom j).label)
    (abc : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label) (Y.atom k).label)
    (sourceABCD : shiftedReal.C.Index
      ((W.atom i).label + (X.atom j).label + (Y.atom k).label)
      (Z.atom l).label)
    (cd : shiftedReal.C.Index (Y.atom k).label (Z.atom l).label)
    (bcd : shiftedReal.C.Index (X.atom j).label
      ((Y.atom k).label + (Z.atom l).label))
    (targetABCD : shiftedReal.C.Index (W.atom i).label
      ((X.atom j).label + (Y.atom k).label + (Z.atom l).label)) :
    let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
    let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
    topRoute W X Y Z (quadLeftPosition W X Y Z qS)
        (quadRightPosition W X Y Z qT) =
      bottomRoute W X Y Z (quadLeftPosition W X Y Z qS)
        (quadRightPosition W X Y Z qT) := by
  classical
  dsimp only
  let qS := quadLeftSlot W X Y Z i j k l ab abc sourceABCD
  let qT := quadRightSlot W X Y Z i j k l cd bcd targetABCD
  let pS := quadLeftPosition W X Y Z qS
  let pT := quadRightPosition W X Y Z qT
  let hS := quadLeftPosition_label W X Y Z i j k l ab abc sourceABCD
  let hST := quadPositionLabelEq W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
  apply AtomHom.ext
  intro h
  have hh : h = hST := Subsingleton.elim _ _
  cases hh
  apply (cast_injective (congrArg
    (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier) hS))
  apply (observeCoefficient_injective
    ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
      (Z.atom l).label))
  funext basis
  have hTop := topCompositeEntry_eq_scalarCoordinate W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
      (kernelIndex
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label) basis)
  have hBottom := bottomCompositeEntry_eq_scalarCoordinate W X Y Z i j k l
    ab abc sourceABCD cd bcd targetABCD
      (kernelIndex
        ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
          (Z.atom l).label) basis)
  rw [coefficientIndex_kernelIndex] at hTop hBottom
  rw [hTop, hBottom]
  exact congrArg
    (fun u : ℝ =>
      bottomCommonSign
          (W.atom i).label (X.atom j).label (Y.atom k).label (Z.atom l).label
          (Y.atom k).shift (Z.atom l).shift
          (rawRowParityOfShifted (W.atom i).label (X.atom j).label ab)
          (rawRowParityOfShifted
            ((W.atom i).label + (X.atom j).label) (Y.atom k).label abc)
          (rawRowParityOfShifted (Y.atom k).label (Z.atom l).label cd)
          (rawRowParityOfShifted (X.atom j).label
            ((Y.atom k).label + (Z.atom l).label) bcd) * u)
      (realComputableShifted_scalarCoordinate_eq
        (W.atom i).label (X.atom j).label
        (Y.atom k).label (Z.atom l).label
        (quadSource i j k l ab abc sourceABCD)
        (quadTarget i j k l cd bcd targetABCD
          (kernelIndex
            ((W.atom i).label + (X.atom j).label + (Y.atom k).label +
              (Z.atom l).label) basis)))

/-! ### Matrix pentagon -/

/-- The endpoint-normalized finite associator satisfies the pentagon.  The
only numerical equality used in the proof is the existing all-coordinate
theorem `realComputableShifted_scalarCoordinate_eq`; everything else is
slot reindexing and transport of its two sides to finite Hom entries. -/
theorem realAssociator_pentagon (W X Y Z : Obj) :
    Hom.comp
      (Hom.comp
        (Tensor.hom shiftedReal.D shiftedReal.C
          (RealAssociator.hom W X Y) (Hom.id shiftedReal.D Z))
        (RealAssociator.hom W (tensorObj X Y) Z))
      (Tensor.hom shiftedReal.D shiftedReal.C (Hom.id shiftedReal.D W)
        (RealAssociator.hom X Y Z)) =
      Hom.comp
        (RealAssociator.hom (tensorObj W X) Y Z)
        (RealAssociator.hom W X (tensorObj Y Z)) := by
  classical
  change topRoute W X Y Z = bottomRoute W X Y Z
  apply Hom.ext
  intro pS pT
  let qS := (Tensor.slots shiftedReal.D shiftedReal.C
    (tensorObj (tensorObj W X) Y) Z).get pS
  let qT := (Tensor.slots shiftedReal.D shiftedReal.C W
    (tensorObj X (tensorObj Y Z))).get pT
  rcases exists_eq_quadLeftSlot W X Y Z qS with
    ⟨i, j, k, l, ab, abc, sourceABCD, hqS⟩
  rcases exists_eq_quadRightSlot W X Y Z qT with
    ⟨i', j', k', l', cd, bcd, targetABCD, hqT⟩
  have hpS : pS = quadLeftPosition W X Y Z
      (quadLeftSlot W X Y Z i j k l ab abc sourceABCD) := by
    apply (RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
      (tensorObj (tensorObj W X) Y) Z).injective
    simpa only [RealAssociatorLaws.slotsEquiv_apply,
      get_quadLeftPosition, qS] using hqS
  have hpT : pT = quadRightPosition W X Y Z
      (quadRightSlot W X Y Z i' j' k' l' cd bcd targetABCD) := by
    apply (RealAssociatorLaws.slotsEquiv shiftedReal.D shiftedReal.C
      W (tensorObj X (tensorObj Y Z))).injective
    simpa only [RealAssociatorLaws.slotsEquiv_apply,
      get_quadRightPosition, qT] using hqT
  subst pS
  subst pT
  by_cases hi : i = i'
  · subst i'
    by_cases hj : j = j'
    · subst j'
      by_cases hk : k = k'
      · subst k'
        by_cases hl : l = l'
        · subst l'
          exact explicitQuadEntry_eq W X Y Z i j k l
            ab abc sourceABCD cd bcd targetABCD
        · have hpos : i ≠ i ∨ j ≠ j ∨ k ≠ k ∨ l ≠ l' :=
            Or.inr (Or.inr (Or.inr hl))
          exact (topRoute_entry_zero_of_exterior_ne W X Y Z
            i j k l ab abc sourceABCD
            i j k l' cd bcd targetABCD hpos).trans
              (bottomRoute_entry_zero_of_exterior_ne W X Y Z
                i j k l ab abc sourceABCD
                i j k l' cd bcd targetABCD hpos).symm
      · have hpos : i ≠ i ∨ j ≠ j ∨ k ≠ k' ∨ l ≠ l' :=
          Or.inr (Or.inr (Or.inl hk))
        exact (topRoute_entry_zero_of_exterior_ne W X Y Z
          i j k l ab abc sourceABCD
          i j k' l' cd bcd targetABCD hpos).trans
            (bottomRoute_entry_zero_of_exterior_ne W X Y Z
              i j k l ab abc sourceABCD
              i j k' l' cd bcd targetABCD hpos).symm
    · have hpos : i ≠ i ∨ j ≠ j' ∨ k ≠ k' ∨ l ≠ l' :=
        Or.inr (Or.inl hj)
      exact (topRoute_entry_zero_of_exterior_ne W X Y Z
        i j k l ab abc sourceABCD
        i j' k' l' cd bcd targetABCD hpos).trans
          (bottomRoute_entry_zero_of_exterior_ne W X Y Z
            i j k l ab abc sourceABCD
            i j' k' l' cd bcd targetABCD hpos).symm
  · have hpos : i ≠ i' ∨ j ≠ j' ∨ k ≠ k' ∨ l ≠ l' :=
      Or.inl hi
    exact (topRoute_entry_zero_of_exterior_ne W X Y Z
      i j k l ab abc sourceABCD
      i' j' k' l' cd bcd targetABCD hpos).trans
        (bottomRoute_entry_zero_of_exterior_ne W X Y Z
          i j k l ab abc sourceABCD
          i' j' k' l' cd bcd targetABCD hpos).symm

end RealAssociatorPentagon

end Superfusion.RMod.FromRawDCT
