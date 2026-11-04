import Superfusion.RMod.FromRawDCT.RealAssociator
import Mathlib.Data.List.NodupEquivFin

/-!
# Evenness laws for the computably shifted real associator

This concrete proof layer specializes the abstract associator extracted from
the raw connector to `realComputableShiftedRawDCT`.  The only concrete input
is the already proved pointwise vanishing of its connector parity.  All
homogeneity transport is then supplied by the stored `TLaws`.
-/

set_option autoImplicit false

universe u

namespace Superfusion.RMod.FromRawDCT

open RawDCT

namespace RealAssociatorLaws

/-! ## Homogeneous coordinate basis vectors -/

/- Every element of `ZMod 2` is its own additive inverse. -/
private theorem zmod2_add_self (i : ZMod 2) : i + i = 0 := by
  revert i
  decide

private theorem leftToCoord_injective (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8) :
    Function.Injective (x.T.leftToCoord a b c) := by
  intro m m' hmm'
  rw [← hx.T.left_ofCoord_toCoord a b c m,
    ← hx.T.left_ofCoord_toCoord a b c m', hmm']

private theorem rightToCoord_injective (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8) :
    Function.Injective (x.T.rightToCoord a b c) := by
  intro m m' hmm'
  rw [← hx.T.right_ofCoord_toCoord a b c m,
    ← hx.T.right_ofCoord_toCoord a b c m', hmm']

/-- A left delta vector has the sum of its two fusion-row parities. -/
private theorem leftDeltaBasis_memGrade (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c) :
    x.T.leftRoute.MemGrade a b c
      (x.C.rowParity a b sourceAB +
        x.C.rowParity (a + b) c sourceABC)
      (x.T.leftOfCoord a b c
        (Associator.leftDelta x a b c sourceAB sourceABC)) := by
  apply leftToCoord_injective x hx a b c
  funext targetAB targetABC
  rw [hx.T.left_toCoord_component, hx.T.left_toCoord_ofCoord]
  change (x.D.algebra (a + b + c)).component
      (x.C.rowParity a b sourceAB +
        x.C.rowParity (a + b) c sourceABC +
        x.C.rowParity a b targetAB +
        x.C.rowParity (a + b) c targetABC)
      (Associator.leftDelta x a b c sourceAB sourceABC
        targetAB targetABC) =
    Associator.leftDelta x a b c sourceAB sourceABC
      targetAB targetABC
  by_cases hAB : targetAB = sourceAB
  · subst targetAB
    by_cases hABC : targetABC = sourceABC
    · subst targetABC
      rw [Associator.leftDelta_source]
      rw [show x.C.rowParity a b sourceAB +
          x.C.rowParity (a + b) c sourceABC +
          x.C.rowParity a b sourceAB +
          x.C.rowParity (a + b) c sourceABC = 0 by
        calc
          _ = (x.C.rowParity a b sourceAB +
                x.C.rowParity a b sourceAB) +
              (x.C.rowParity (a + b) c sourceABC +
                x.C.rowParity (a + b) c sourceABC) := by ac_rfl
          _ = 0 := by rw [zmod2_add_self, zmod2_add_self, zero_add]]
      exact (hx.D.algebra_laws (a + b + c)).one_mem
    · rw [Associator.leftDelta_off_second x a b c sourceAB
        sourceABC targetABC hABC]
      exact (hx.D.algebra_laws (a + b + c)).component_zero _
  · rw [Associator.leftDelta_off_first x a b c sourceAB targetAB
      sourceABC targetABC hAB]
    exact (hx.D.algebra_laws (a + b + c)).component_zero _

/-- A right delta vector has the analogous sum of row parities. -/
private theorem rightDeltaBasis_memGrade (x : RawDCTData)
    (hx : RawDCTLaws x) (a b c : ZMod 8)
    (sourceBC : x.C.Index b c) (sourceABC : x.C.Index a (b + c)) :
    x.T.rightRoute.MemGrade a b c
      (x.C.rowParity b c sourceBC +
        x.C.rowParity a (b + c) sourceABC)
      (x.T.rightOfCoord a b c
        (Associator.rightDelta x a b c sourceBC sourceABC)) := by
  apply rightToCoord_injective x hx a b c
  funext targetBC targetABC
  rw [hx.T.right_toCoord_component, hx.T.right_toCoord_ofCoord]
  change (x.D.algebra (a + b + c)).component
      (x.C.rowParity b c sourceBC +
        x.C.rowParity a (b + c) sourceABC +
        x.C.rowParity b c targetBC +
        x.C.rowParity a (b + c) targetABC)
      (Associator.rightDelta x a b c sourceBC sourceABC
        targetBC targetABC) =
    Associator.rightDelta x a b c sourceBC sourceABC
      targetBC targetABC
  by_cases hBC : targetBC = sourceBC
  · subst targetBC
    by_cases hABC : targetABC = sourceABC
    · subst targetABC
      rw [Associator.rightDelta_source]
      rw [show x.C.rowParity b c sourceBC +
          x.C.rowParity a (b + c) sourceABC +
          x.C.rowParity b c sourceBC +
          x.C.rowParity a (b + c) sourceABC = 0 by
        calc
          _ = (x.C.rowParity b c sourceBC +
                x.C.rowParity b c sourceBC) +
              (x.C.rowParity a (b + c) sourceABC +
                x.C.rowParity a (b + c) sourceABC) := by ac_rfl
          _ = 0 := by rw [zmod2_add_self, zmod2_add_self, zero_add]]
      exact (hx.D.algebra_laws (a + b + c)).one_mem
    · rw [Associator.rightDelta_off_second x a b c sourceBC
        sourceABC targetABC hABC]
      exact (hx.D.algebra_laws (a + b + c)).component_zero _
  · rw [Associator.rightDelta_off_first x a b c sourceBC targetBC
      sourceABC targetABC hBC]
    exact (hx.D.algebra_laws (a + b + c)).component_zero _

/-! ## Connector coefficients at zero connector parity -/

theorem homCoefficient_memGrade_of_parity_zero
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (hp : x.T.parity a b c = 0)
    (sourceAB : x.C.Index a b) (sourceABC : x.C.Index (a + b) c)
    (targetBC : x.C.Index b c) (targetABC : x.C.Index a (b + c)) :
    (x.D.algebra (a + b + c)).MemGrade
      (x.C.rowParity a b sourceAB +
        x.C.rowParity (a + b) c sourceABC +
        x.C.rowParity b c targetBC +
        x.C.rowParity a (b + c) targetABC)
      (Associator.homCoefficient x a b c sourceAB sourceABC
        targetBC targetABC) := by
  let basis := x.T.leftOfCoord a b c
    (Associator.leftDelta x a b c sourceAB sourceABC)
  have hm := hx.T.hom_grade a b c
    (x.C.rowParity a b sourceAB +
      x.C.rowParity (a + b) c sourceABC) basis
    (leftDeltaBasis_memGrade x hx a b c sourceAB sourceABC)
  rw [hp, add_zero] at hm
  have hcoord := congrArg
    (fun m => x.T.rightToCoord a b c m targetBC targetABC) hm
  rw [hx.T.right_toCoord_component] at hcoord
  change (x.D.algebra (a + b + c)).component
      (x.C.rowParity a b sourceAB +
        x.C.rowParity (a + b) c sourceABC +
        x.C.rowParity b c targetBC +
        x.C.rowParity a (b + c) targetABC)
      (Associator.homCoefficient x a b c sourceAB sourceABC
        targetBC targetABC) =
    Associator.homCoefficient x a b c sourceAB sourceABC
      targetBC targetABC
  simpa only [basis, Associator.homCoefficient] using hcoord

theorem invCoefficient_memGrade_of_parity_zero
    (x : RawDCTData) (hx : RawDCTLaws x) (a b c : ZMod 8)
    (hp : x.T.parity a b c = 0)
    (sourceBC : x.C.Index b c) (sourceABC : x.C.Index a (b + c))
    (targetAB : x.C.Index a b) (targetABC : x.C.Index (a + b) c) :
    (x.D.algebra (a + b + c)).MemGrade
      (x.C.rowParity b c sourceBC +
        x.C.rowParity a (b + c) sourceABC +
        x.C.rowParity a b targetAB +
        x.C.rowParity (a + b) c targetABC)
      (Associator.invCoefficient x a b c sourceBC sourceABC
        targetAB targetABC) := by
  let basis := x.T.rightOfCoord a b c
    (Associator.rightDelta x a b c sourceBC sourceABC)
  have hm := hx.T.inv_grade a b c
    (x.C.rowParity b c sourceBC +
      x.C.rowParity a (b + c) sourceABC) basis
    (rightDeltaBasis_memGrade x hx a b c sourceBC sourceABC)
  rw [hp, add_zero] at hm
  have hcoord := congrArg
    (fun m => x.T.leftToCoord a b c m targetAB targetABC) hm
  rw [hx.T.left_toCoord_component] at hcoord
  change (x.D.algebra (a + b + c)).component
      (x.C.rowParity b c sourceBC +
        x.C.rowParity a (b + c) sourceABC +
        x.C.rowParity a b targetAB +
        x.C.rowParity (a + b) c targetABC)
      (Associator.invCoefficient x a b c sourceBC sourceABC
        targetAB targetABC) =
    Associator.invCoefficient x a b c sourceBC sourceABC
      targetAB targetABC
  simpa only [basis, Associator.invCoefficient] using hcoord

/-! ## Specialization to the computable real shift -/

private abbrev shiftedReal : RawDCTData :=
  realComputableShiftedRawDCT.data

private theorem shiftedReal_parity_eq_zero (a b c : ZMod 8) :
    shiftedReal.T.parity a b c = 0 := by
  simpa [shiftedReal, rawParity] using
    realComputableShiftedRawDCT_parity_eq_zero
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd b)
      (Multiplicative.ofAdd c)

/-- Each forward coefficient of the shifted real connector has exactly the
sum of the four source/target fusion-row parities. -/
theorem realHomCoefficient_memGrade (a b c : ZMod 8)
    (sourceAB : shiftedReal.C.Index a b)
    (sourceABC : shiftedReal.C.Index (a + b) c)
    (targetBC : shiftedReal.C.Index b c)
    (targetABC : shiftedReal.C.Index a (b + c)) :
    (shiftedReal.D.algebra (a + b + c)).MemGrade
      (shiftedReal.C.rowParity a b sourceAB +
        shiftedReal.C.rowParity (a + b) c sourceABC +
        shiftedReal.C.rowParity b c targetBC +
        shiftedReal.C.rowParity a (b + c) targetABC)
      (Associator.homCoefficient shiftedReal a b c sourceAB sourceABC
        targetBC targetABC) :=
  homCoefficient_memGrade_of_parity_zero shiftedReal
    realComputableShiftedRawDCT.laws a b c
    (shiftedReal_parity_eq_zero a b c) sourceAB sourceABC
    targetBC targetABC

/-- Each inverse coefficient has the same source/target degree formula. -/
theorem realInvCoefficient_memGrade (a b c : ZMod 8)
    (sourceBC : shiftedReal.C.Index b c)
    (sourceABC : shiftedReal.C.Index a (b + c))
    (targetAB : shiftedReal.C.Index a b)
    (targetABC : shiftedReal.C.Index (a + b) c) :
    (shiftedReal.D.algebra (a + b + c)).MemGrade
      (shiftedReal.C.rowParity b c sourceBC +
        shiftedReal.C.rowParity a (b + c) sourceABC +
        shiftedReal.C.rowParity a b targetAB +
        shiftedReal.C.rowParity (a + b) c targetABC)
      (Associator.invCoefficient shiftedReal a b c sourceBC sourceABC
        targetAB targetABC) :=
  invCoefficient_memGrade_of_parity_zero shiftedReal
    realComputableShiftedRawDCT.laws a b c
    (shiftedReal_parity_eq_zero a b c) sourceBC sourceABC
    targetAB targetABC

@[simp] private theorem rowParity_castIndex (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    x.C.rowParity a' b' (Associator.castIndex x ha hb r) =
      x.C.rowParity a b r := by
  subst a'
  subst b'
  rfl

@[simp] private theorem castIndex_symm_cancel (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a' b') :
    Associator.castIndex x ha hb
      (Associator.castIndex x ha.symm hb.symm r) = r := by
  subst a'
  subst b'
  rfl

/- Transporting a fusion row in two stages is the same as transporting it
along the composite endpoint equalities. -/
private theorem castIndex_trans (x : RawDCTData)
    {a b a' b' a'' b'' : ZMod 8}
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (r : x.C.Index a b) :
    Associator.castIndex x ha' hb' (Associator.castIndex x ha hb r) =
      Associator.castIndex x (ha.trans ha') (hb.trans hb') r := by
  subst a'
  subst b'
  subst a''
  subst b''
  rfl

/- The result of index transport does not depend on the chosen equality
proofs between fixed endpoints. -/
private theorem castIndex_proof_irrel (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha ha' : a = a') (hb hb' : b = b')
    (r : x.C.Index a b) :
    Associator.castIndex x ha hb r = Associator.castIndex x ha' hb' r := by
  subst a'
  subst b'
  rfl

/- Equality of tensor slots transports their stored fusion rows along the
induced endpoint equalities. -/
private theorem slotFusion_cast_of_eq (x : RawDCTData) (X Y : Obj)
    (q q' : Tensor.Slot x.D x.C X Y) (h : q = q') :
    Associator.castIndex x
        (congrArg (fun s => (X.atom s.left).label) h)
        (congrArg (fun s => (Y.atom s.right).label) h) q.fusion =
      q'.fusion := by
  subst q'
  rfl

/- The actual connector coefficient is invariant under simultaneous
transport of its three labels and four fusion rows. -/
private theorem homCoefficient_transport (x : RawDCTData)
    {a b c a' b' c' : ZMod 8}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (ab : x.C.Index a b) (abc : x.C.Index (a + b) c)
    (bc : x.C.Index b c) (a_bc : x.C.Index a (b + c)) :
    Associator.homCoefficient x a b c ab abc bc a_bc =
      cast
        (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
          (congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc)).symm
        (Associator.homCoefficient x a' b' c'
          (Associator.castIndex x ha hb ab)
          (Associator.castIndex x (congrArg₂ (· + ·) ha hb) hc abc)
          (Associator.castIndex x hb hc bc)
          (Associator.castIndex x ha (congrArg₂ (· + ·) hb hc) a_bc)) := by
  subst a'
  subst b'
  subst c'
  rfl

/- The inverse connector coefficient obeys the same simultaneous transport
law, with its two right rows followed by its two left rows. -/
private theorem invCoefficient_transport (x : RawDCTData)
    {a b c a' b' c' : ZMod 8}
    (ha : a = a') (hb : b = b') (hc : c = c')
    (bc : x.C.Index b c) (a_bc : x.C.Index a (b + c))
    (ab : x.C.Index a b) (abc : x.C.Index (a + b) c) :
    Associator.invCoefficient x a b c bc a_bc ab abc =
      cast
        (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
          (congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc)).symm
        (Associator.invCoefficient x a' b' c'
          (Associator.castIndex x hb hc bc)
          (Associator.castIndex x ha (congrArg₂ (· + ·) hb hc) a_bc)
          (Associator.castIndex x ha hb ab)
          (Associator.castIndex x (congrArg₂ (· + ·) ha hb) hc abc)) := by
  subst a'
  subst b'
  subst c'
  rfl

/- `congrArg` commutes with reversing an equality for the purpose of type
transport. -/
private theorem cast_congrArg_symm {A : Type*} (F : A → Type*)
    {a b : A} (h : a = b) (x : F b) :
    cast (congrArg F h).symm x = cast (congrArg F h.symm) x := by
  subst b
  rfl

/- Two consecutive transports in a type family are transport along the
composite equality. -/
private theorem cast_congrArg_trans {A : Type*} (F : A → Type*)
    {a b c : A} (hab : a = b) (hbc : b = c) (x : F a) :
    cast (congrArg F hbc) (cast (congrArg F hab) x) =
      cast (congrArg F (hab.trans hbc)) x := by
  subst b
  subst c
  rfl

/- Nested transports against two forward equalities combine without exposing
the implementation of `cast`. -/
private theorem cast_congrArg_symm_trans {A : Type*} (F : A → Type*)
    {a b c : A} (hab : a = b) (hbc : b = c) (x : F c) :
    cast (congrArg F hab).symm (cast (congrArg F hbc).symm x) =
      cast (congrArg F (hab.trans hbc)).symm x := by
  subst b
  subst c
  rfl

/- Transport between fixed endpoint types is independent of the proof of
equality used to perform it. -/
private theorem cast_proof_irrel {A B : Sort u} (h h' : A = B) (x : A) :
    cast h x = cast h' x := by
  rw [Subsingleton.elim h h']

/-- Transporting a coefficient along an equality of labels preserves its
stored algebra degree. -/
private theorem memGrade_cast_symm (dD : DData) {a b : ZMod 8}
    (h : a = b) (i : ZMod 2) (q : (dD.algebra b).carrier)
    (hq : (dD.algebra b).MemGrade i q) :
    (dD.algebra a).MemGrade i
      (cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h).symm q) := by
  subst b
  exact hq

/-! ## Finite enumeration bridges -/

/-- Proof-layer additive group on one atomic Hom space. -/
@[implicit_reducible]
private def atomHomAddCommGroup (dD : DData) (hD : DLaws dD)
    (X Y : Atom) : AddCommGroup (AtomHom dD X Y) := by
  letI : Zero (AtomHom dD X Y) := ⟨AtomHom.zero dD X Y⟩
  letI : Add (AtomHom dD X Y) := ⟨AtomHom.add⟩
  letI : Neg (AtomHom dD X Y) := ⟨AtomHom.neg⟩
  letI : Sub (AtomHom dD X Y) :=
    ⟨fun f g => AtomHom.add f (AtomHom.neg g)⟩
  exact
    { add_assoc := AtomHom.add_assoc hD
      zero_add := AtomHom.zero_add hD
      add_zero := AtomHom.add_zero hD
      neg_add_cancel := AtomHom.neg_add hD
      add_comm := AtomHom.add_comm hD
      sub_eq_add_neg := fun _ _ => rfl
      nsmul := nsmulRec
      zsmul := zsmulRec }

/-- Proof-layer additive group on one stored coefficient algebra. -/
@[implicit_reducible]
private def algebraAddCommGroup (d : SuperAlgebraData ℝ)
    (h : SuperAlgebraLaws d) : AddCommGroup d.carrier := by
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

private instance atomHomAddCommGroupInstance {dD : DData}
    [hD : Fact (DLaws dD)] {X Y : Atom} :
    AddCommGroup (AtomHom dD X Y) :=
  atomHomAddCommGroup dD hD.out X Y

private instance algebraAddCommGroupInstance (d : SuperAlgebraData ℝ)
    [h : Fact (SuperAlgebraLaws d)] : AddCommGroup d.carrier :=
  algebraAddCommGroup d h.out

private theorem atomHom_finSum_eq_sum {dD : DData} [Fact (DLaws dD)]
    {X Y : Atom} {n : ℕ} (f : Fin n → AtomHom dD X Y) :
    AtomHom.finSum n f = ∑ i, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [AtomHom.finSum, ih, Fin.sum_univ_castSucc]
      rfl

private theorem rawFinSum_eq_sum (d : SuperAlgebraData ℝ)
    [Fact (SuperAlgebraLaws d)] {n : ℕ} (f : Fin n → d.carrier) :
    CData.rawFinSum d f = ∑ i, f i := by
  unfold CData.rawFinSum
  change (List.ofFn f).sum = ∑ i, f i
  exact List.sum_ofFn

/-! The following transport lemmas keep the inverse identities in the
coefficient algebra in which the stored raw connector laws are stated. -/

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

private theorem cast_algebra_one_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier) :
    cast h (dD.algebra a).one = (dD.algebra b).one := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem cast_algebra_zero_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier) :
    cast h (dD.algebra a).zero = (dD.algebra b).zero := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem cast_cast_eq {A B C : Type} (hAB : A = B) (hBC : B = C)
    (u : A) : cast hBC (cast hAB u) = cast (hAB.trans hBC) u := by
  subst B
  subst C
  rfl

private theorem cast_rawFinSum (dD : DData) {a b : ZMod 8}
    (h : a = b) {n : ℕ} (f : Fin n → (dD.algebra a).carrier) :
    cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h)
        (CData.rawFinSum (dD.algebra a) f) =
      CData.rawFinSum (dD.algebra b) (fun i =>
        cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h)
          (f i)) := by
  subst b
  rfl

private theorem rawFinSum_congr (d : SuperAlgebraData ℝ) {n : ℕ}
    {f g : Fin n → d.carrier} (h : ∀ i, f i = g i) :
    CData.rawFinSum d f = CData.rawFinSum d g := by
  exact congrArg (CData.rawFinSum d) (funext h)

/-- Reading a coefficient commutes with the fixed atomic finite sum. -/
private theorem coeff_finSum {dD : DData} (hD : DLaws dD)
    {X Y : Atom} (hXY : X.label = Y.label)
    {n : ℕ} (f : Fin n → AtomHom dD X Y) :
    (AtomHom.finSum n f).coeff hXY =
      CData.rawFinSum (dD.algebra X.label) (fun i => (f i).coeff hXY) := by
  letI : Fact (DLaws dD) := ⟨hD⟩
  letI : Fact (SuperAlgebraLaws (dD.algebra X.label)) :=
    ⟨hD.algebra_laws X.label⟩
  let coeffHom : AtomHom dD X Y →+ (dD.algebra X.label).carrier :=
    { toFun := fun q => q.coeff hXY
      map_zero' := AtomHom.coeff_zero hXY
      map_add' := fun p q => AtomHom.coeff_add p q hXY }
  rw [atomHom_finSum_eq_sum, rawFinSum_eq_sum]
  exact _root_.map_sum coeffHom (fun i => f i) Finset.univ

private theorem slots_mem_all (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Tensor.Slot dD dC X Y) :
    q ∈ Tensor.slots dD dC X Y := by
  rcases q with ⟨i, j, r⟩
  simp [Tensor.slots]

/-- The canonical slot list is a bijective enumeration of the dependent
triple `(left index, right index, fusion row)`. -/
def slotsEquiv (dD : DData) (dC : CData dD) (X Y : Obj) :
    Fin (Tensor.slots dD dC X Y).length ≃ Tensor.Slot dD dC X Y :=
  (Tensor.slots_nodup dD dC X Y).getEquivOfForallMemList
    (Tensor.slots dD dC X Y) (slots_mem_all dD dC X Y)

@[simp] theorem slotsEquiv_apply (dD : DData) (dC : CData dD)
    (X Y : Obj) (i : Fin (Tensor.slots dD dC X Y).length) :
    slotsEquiv dD dC X Y i = (Tensor.slots dD dC X Y).get i :=
  rfl

/-- Summation over the dependent slot type is the corresponding iterated
sum over the two object positions and the stored fusion row. -/
theorem sum_slots {dD : DData} {dC : CData dD}
    {M : Type*} [AddCommMonoid M] (X Y : Obj)
    (F : Tensor.Slot dD dC X Y → M) :
    (∑ q : Tensor.Slot dD dC X Y, F q) =
      ∑ i : Fin X.size, ∑ j : Fin Y.size,
        ∑ r : dC.Index (X.atom i).label (Y.atom j).label,
          F ⟨i, j, r⟩ := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_sigma]

/-- Coordinates for a right-associated slot, with the inner tensor position
replaced by the actual `Y ⊗ Z` slot that it enumerates. -/
abbrev RightSlotCoordinates (dD : DData) (dC : CData dD)
    (X Y Z : Obj) :=
  (i : Fin X.size) ×
    (yz : Tensor.Slot dD dC Y Z) ×
      dC.Index (X.atom i).label (Tensor.slotAtom dD dC Y Z yz).label

/-- Packing the five original right-route coordinates into the nested slot.
The dependent transport of the outer fusion row is supplied by
`Equiv.sigmaCongr`; no row is recomputed. -/
def rightSlotPack (dD : DData) (dC : CData dD)
    (X Y Z : Obj) :
    RightSlotCoordinates dD dC X Y Z ≃
      Tensor.Slot dD dC X (Tensor.obj dD dC Y Z) :=
  (Equiv.sigmaCongrRight fun i =>
    Equiv.sigmaCongr (slotsEquiv dD dC Y Z) fun j =>
      Equiv.refl
        (dC.Index (X.atom i).label
          ((Tensor.obj dD dC Y Z).atom j).label)).symm

@[simp] theorem rightSlotPack_left (dD : DData) (dC : CData dD)
    (X Y Z : Obj) (q : RightSlotCoordinates dD dC X Y Z) :
    (rightSlotPack dD dC X Y Z q).left = q.1 :=
  rfl

@[simp] theorem rightSlotPack_inner (dD : DData) (dC : CData dD)
    (X Y Z : Obj) (q : RightSlotCoordinates dD dC X Y Z) :
    (Tensor.slots dD dC Y Z).get
        (rightSlotPack dD dC X Y Z q).right = q.2.1 := by
  change slotsEquiv dD dC Y Z
      ((slotsEquiv dD dC Y Z).symm q.2.1) = q.2.1
  exact (slotsEquiv dD dC Y Z).apply_symm_apply q.2.1

/-- Reindexing a sum over nested right slots exposes exactly the two
connector middle rows after the three original object positions. -/
theorem sum_rightSlotCoordinates {dD : DData} {dC : CData dD}
    {M : Type*} [AddCommMonoid M] (X Y Z : Obj)
    (F : Tensor.Slot dD dC X (Tensor.obj dD dC Y Z) → M) :
    (∑ qR, F qR) =
      ∑ i : Fin X.size,
        ∑ yz : Tensor.Slot dD dC Y Z,
          ∑ a_bc : dC.Index (X.atom i).label
              (Tensor.slotAtom dD dC Y Z yz).label,
            F (rightSlotPack dD dC X Y Z ⟨i, yz, a_bc⟩) := by
  calc
    (∑ qR, F qR) =
        ∑ q : RightSlotCoordinates dD dC X Y Z,
          F (rightSlotPack dD dC X Y Z q) :=
      ((rightSlotPack dD dC X Y Z).sum_comp F).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [Fintype.sum_sigma]

/-- Coordinates for a left-associated slot, exposing the actual `X ⊗ Y`
slot together with the third object position and the outer fusion row. -/
abbrev LeftSlotCoordinates (dD : DData) (dC : CData dD)
    (X Y Z : Obj) :=
  (xy : Tensor.Slot dD dC X Y) ×
    (k : Fin Z.size) ×
      dC.Index (Tensor.slotAtom dD dC X Y xy).label (Z.atom k).label

/-- Packing the four exposed left-route coordinates into the nested slot. -/
def leftSlotPack (dD : DData) (dC : CData dD)
    (X Y Z : Obj) :
    LeftSlotCoordinates dD dC X Y Z ≃
      Tensor.Slot dD dC (Tensor.obj dD dC X Y) Z :=
  (Equiv.sigmaCongr (slotsEquiv dD dC X Y) fun i =>
    Equiv.refl
      ((k : Fin Z.size) ×
        dC.Index ((Tensor.obj dD dC X Y).atom i).label
          (Z.atom k).label)).symm

@[simp] theorem leftSlotPack_inner (dD : DData) (dC : CData dD)
    (X Y Z : Obj) (q : LeftSlotCoordinates dD dC X Y Z) :
    (Tensor.slots dD dC X Y).get
        (leftSlotPack dD dC X Y Z q).left = q.1 := by
  change slotsEquiv dD dC X Y
      ((slotsEquiv dD dC X Y).symm q.1) = q.1
  exact (slotsEquiv dD dC X Y).apply_symm_apply q.1

@[simp] theorem leftSlotPack_right (dD : DData) (dC : CData dD)
    (X Y Z : Obj) (q : LeftSlotCoordinates dD dC X Y Z) :
    (leftSlotPack dD dC X Y Z q).right = q.2.1 :=
  by
    change ((leftSlotPack dD dC X Y Z).symm
      (leftSlotPack dD dC X Y Z q)).2.1 = q.2.1
    rw [Equiv.symm_apply_apply]

/-- Reindexing a sum over nested left slots exposes the inner `X ⊗ Y`
slot, the original `Z` position, and the outer fusion row. -/
theorem sum_leftSlotCoordinates {dD : DData} {dC : CData dD}
    {M : Type*} [AddCommMonoid M] (X Y Z : Obj)
    (F : Tensor.Slot dD dC (Tensor.obj dD dC X Y) Z → M) :
    (∑ qL, F qL) =
      ∑ xy : Tensor.Slot dD dC X Y,
        ∑ k : Fin Z.size,
          ∑ abc : dC.Index (Tensor.slotAtom dD dC X Y xy).label
              (Z.atom k).label,
            F (leftSlotPack dD dC X Y Z ⟨xy, k, abc⟩) := by
  calc
    (∑ qL, F qL) =
        ∑ q : LeftSlotCoordinates dD dC X Y Z,
          F (leftSlotPack dD dC X Y Z q) :=
      ((leftSlotPack dD dC X Y Z).sum_comp F).symm
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro xy _
      rw [Fintype.sum_sigma]

/-! ## Evenness of the concrete associator entries -/

/-- Every forward matrix entry is categorically even. -/
theorem realHomEntry_even (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom.MemGrade 0
      (Associator.homEntry shiftedReal X Y Z qL qR) := by
  let xy := (Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left
  let yz := (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right
  by_cases hX : xy.left = qR.left
  · by_cases hY : xy.right = yz.left
    · by_cases hZ : qL.right = yz.right
      · let a := X.atom xy.left
        let b := Y.atom xy.right
        let c := Z.atom qL.right
        have hBCLeft : (Y.atom yz.left).label = b.label := by
          simpa [b] using congrArg (fun i => (Y.atom i).label) hY.symm
        have hBCRight : (Z.atom yz.right).label = c.label := by
          simpa [c] using congrArg (fun i => (Z.atom i).label) hZ.symm
        let bc : shiftedReal.C.Index b.label c.label :=
          Associator.castIndex shiftedReal hBCLeft hBCRight yz.fusion
        have hALeft : (X.atom qR.left).label = a.label := by
          simpa [a] using congrArg (fun i => (X.atom i).label) hX.symm
        have hYZLabel :
            ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom qR.right).label =
              b.label + c.label := by
          change (Y.atom yz.left).label + (Z.atom yz.right).label = _
          rw [hBCLeft, hBCRight]
        let a_bc : shiftedReal.C.Index a.label (b.label + c.label) :=
          Associator.castIndex shiftedReal hALeft hYZLabel qR.fusion
        have hXYLabel :
            ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom qL.left).label =
              a.label + b.label := by
          rfl
        let abc : shiftedReal.C.Index (a.label + b.label) c.label :=
          Associator.castIndex shiftedReal hXYLabel rfl qL.fusion
        have hLabel :
            (Tensor.slotAtom shiftedReal.D shiftedReal.C
                (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL).label =
              (Tensor.slotAtom shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR).label := by
          change ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
                qL.left).label + (Z.atom qL.right).label =
            (X.atom qR.left).label +
              ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
                qR.right).label
          rw [hXYLabel, hYZLabel, hALeft]
          exact _root_.add_assoc _ _ _
        rw [show Associator.homEntry shiftedReal X Y Z qL qR =
            AtomHom.ofLabelEq hLabel
              (Associator.homCoefficient shiftedReal a.label b.label c.label
                xy.fusion abc bc a_bc) by
          simp only [Associator.homEntry, xy, yz, hX, hY, hZ,
            dite_true]
          rfl]
        intro hEndpoint
        rw [AtomHom.coeff_ofLabelEq]
        have hABCParity :
            shiftedReal.C.rowParity
                ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
                  qL.left).label
                (Z.atom qL.right).label qL.fusion =
              shiftedReal.C.rowParity (a.label + b.label) c.label abc := by
          simpa only [abc, a, b, c] using
            (rowParity_castIndex shiftedReal hXYLabel rfl qL.fusion).symm
        have hBCParity :
            shiftedReal.C.rowParity (Y.atom yz.left).label
                (Z.atom yz.right).label yz.fusion =
              shiftedReal.C.rowParity b.label c.label bc := by
          simpa only [bc, b, c] using
            (rowParity_castIndex shiftedReal hBCLeft hBCRight yz.fusion).symm
        have hA_BCParity :
            shiftedReal.C.rowParity (X.atom qR.left).label
                ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
                  qR.right).label qR.fusion =
              shiftedReal.C.rowParity a.label (b.label + c.label) a_bc := by
          simpa only [a_bc, a, b, c] using
            (rowParity_castIndex shiftedReal hALeft hYZLabel qR.fusion).symm
        have hgrade :
            0 +
                (Tensor.slotAtom shiftedReal.D shiftedReal.C
                  (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL).shift +
                (Tensor.slotAtom shiftedReal.D shiftedReal.C X
                  (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR).shift =
              shiftedReal.C.rowParity a.label b.label xy.fusion +
                shiftedReal.C.rowParity (a.label + b.label) c.label abc +
                shiftedReal.C.rowParity b.label c.label bc +
                shiftedReal.C.rowParity a.label (b.label + c.label) a_bc := by
          change 0 +
              ((X.atom xy.left).shift + (Y.atom xy.right).shift +
                  shiftedReal.C.rowParity a.label b.label xy.fusion +
                (Z.atom qL.right).shift +
                  shiftedReal.C.rowParity
                    ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
                      qL.left).label
                    (Z.atom qL.right).label qL.fusion) +
              ((X.atom qR.left).shift +
                  ((Y.atom yz.left).shift + (Z.atom yz.right).shift +
                    shiftedReal.C.rowParity (Y.atom yz.left).label
                      (Z.atom yz.right).label yz.fusion) +
                shiftedReal.C.rowParity (X.atom qR.left).label
                  ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
                    qR.right).label qR.fusion) = _
          rw [hABCParity, hBCParity, hA_BCParity,
            ← congrArg (fun i => (X.atom i).shift) hX,
            ← congrArg (fun i => (Y.atom i).shift) hY,
            ← congrArg (fun i => (Z.atom i).shift) hZ]
          calc
            _ = (shiftedReal.C.rowParity a.label b.label xy.fusion +
                    shiftedReal.C.rowParity (a.label + b.label) c.label abc +
                    shiftedReal.C.rowParity b.label c.label bc +
                    shiftedReal.C.rowParity a.label (b.label + c.label) a_bc) +
                  ((X.atom xy.left).shift + (X.atom xy.left).shift) +
                  ((Y.atom xy.right).shift + (Y.atom xy.right).shift) +
                  ((Z.atom qL.right).shift + (Z.atom qL.right).shift) := by
                ac_rfl
            _ = _ := by
              rw [zmod2_add_self, zmod2_add_self, zmod2_add_self,
                add_zero, add_zero, add_zero]
        rw [hgrade]
        exact realHomCoefficient_memGrade a.label b.label c.label
          xy.fusion abc bc a_bc
      · have hX' :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              qL.left).left = qR.left := by simpa [xy] using hX
        have hY' :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              qL.left).right =
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                qR.right).left := by simpa [xy, yz] using hY
        have hZ' : qL.right ≠
            ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
              qR.right).right := by simpa [yz] using hZ
        unfold Associator.homEntry
        dsimp only
        rw [dif_pos hX', dif_pos hY', dif_neg hZ']
        exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0
    · have hX' :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              qL.left).left = qR.left := by simpa [xy] using hX
      have hY' :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              qL.left).right ≠
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                qR.right).left := by simpa [xy, yz] using hY
      unfold Associator.homEntry
      dsimp only
      rw [dif_pos hX', dif_neg hY']
      exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0
  · have hX' :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            qL.left).left ≠ qR.left := by simpa [xy] using hX
    unfold Associator.homEntry
    dsimp only
    rw [dif_neg hX']
    exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0

/-- Every inverse matrix entry is categorically even. -/
theorem realInvEntry_even (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom.MemGrade 0
      (Associator.invEntry shiftedReal X Y Z qR qL) := by
  let xy := (Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left
  let yz := (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right
  by_cases hX : xy.left = qR.left
  · by_cases hY : xy.right = yz.left
    · by_cases hZ : qL.right = yz.right
      · let a := X.atom xy.left
        let b := Y.atom xy.right
        let c := Z.atom qL.right
        have hBCLeft : (Y.atom yz.left).label = b.label := by
          simpa [b] using congrArg (fun i => (Y.atom i).label) hY.symm
        have hBCRight : (Z.atom yz.right).label = c.label := by
          simpa [c] using congrArg (fun i => (Z.atom i).label) hZ.symm
        let bc : shiftedReal.C.Index b.label c.label :=
          Associator.castIndex shiftedReal hBCLeft hBCRight yz.fusion
        have hALeft : (X.atom qR.left).label = a.label := by
          simpa [a] using congrArg (fun i => (X.atom i).label) hX.symm
        have hYZLabel :
            ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom qR.right).label =
              b.label + c.label := by
          change (Y.atom yz.left).label + (Z.atom yz.right).label = _
          rw [hBCLeft, hBCRight]
        let a_bc : shiftedReal.C.Index a.label (b.label + c.label) :=
          Associator.castIndex shiftedReal hALeft hYZLabel qR.fusion
        have hXYLabel :
            ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom qL.left).label =
              a.label + b.label := by
          rfl
        let abc : shiftedReal.C.Index (a.label + b.label) c.label :=
          Associator.castIndex shiftedReal hXYLabel rfl qL.fusion
        have hLabel :
            (Tensor.slotAtom shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR).label =
              (Tensor.slotAtom shiftedReal.D shiftedReal.C
                (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL).label := by
          change (X.atom qR.left).label +
                ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
                  qR.right).label =
            ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
                qL.left).label + (Z.atom qL.right).label
          rw [hXYLabel, hYZLabel, hALeft]
          exact (_root_.add_assoc _ _ _).symm
        rw [show Associator.invEntry shiftedReal X Y Z qR qL =
            AtomHom.ofLabelEq hLabel
              (cast
                (congrArg
                  (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
                  hLabel).symm
                (Associator.invCoefficient shiftedReal
                  a.label b.label c.label bc a_bc xy.fusion abc)) by
          simp only [Associator.invEntry, xy, yz, hX, hY, hZ,
            dite_true]
          rfl]
        intro hEndpoint
        rw [AtomHom.coeff_ofLabelEq]
        have hABCParity :
            shiftedReal.C.rowParity
                ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
                  qL.left).label
                (Z.atom qL.right).label qL.fusion =
              shiftedReal.C.rowParity (a.label + b.label) c.label abc := by
          simpa only [abc, a, b, c] using
            (rowParity_castIndex shiftedReal hXYLabel rfl qL.fusion).symm
        have hBCParity :
            shiftedReal.C.rowParity (Y.atom yz.left).label
                (Z.atom yz.right).label yz.fusion =
              shiftedReal.C.rowParity b.label c.label bc := by
          simpa only [bc, b, c] using
            (rowParity_castIndex shiftedReal hBCLeft hBCRight yz.fusion).symm
        have hA_BCParity :
            shiftedReal.C.rowParity (X.atom qR.left).label
                ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
                  qR.right).label qR.fusion =
              shiftedReal.C.rowParity a.label (b.label + c.label) a_bc := by
          simpa only [a_bc, a, b, c] using
            (rowParity_castIndex shiftedReal hALeft hYZLabel qR.fusion).symm
        have hgrade :
            0 +
                (Tensor.slotAtom shiftedReal.D shiftedReal.C X
                  (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR).shift +
                (Tensor.slotAtom shiftedReal.D shiftedReal.C
                  (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL).shift =
              shiftedReal.C.rowParity b.label c.label bc +
                shiftedReal.C.rowParity a.label (b.label + c.label) a_bc +
                shiftedReal.C.rowParity a.label b.label xy.fusion +
                shiftedReal.C.rowParity (a.label + b.label) c.label abc := by
          change 0 +
              ((X.atom qR.left).shift +
                  ((Y.atom yz.left).shift + (Z.atom yz.right).shift +
                    shiftedReal.C.rowParity (Y.atom yz.left).label
                      (Z.atom yz.right).label yz.fusion) +
                shiftedReal.C.rowParity (X.atom qR.left).label
                  ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
                    qR.right).label qR.fusion) +
              ((X.atom xy.left).shift + (Y.atom xy.right).shift +
                  shiftedReal.C.rowParity a.label b.label xy.fusion +
                (Z.atom qL.right).shift +
                  shiftedReal.C.rowParity
                    ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
                      qL.left).label
                    (Z.atom qL.right).label qL.fusion) = _
          rw [hABCParity, hBCParity, hA_BCParity,
            ← congrArg (fun i => (X.atom i).shift) hX,
            ← congrArg (fun i => (Y.atom i).shift) hY,
            ← congrArg (fun i => (Z.atom i).shift) hZ]
          calc
            _ = (shiftedReal.C.rowParity b.label c.label bc +
                    shiftedReal.C.rowParity a.label (b.label + c.label) a_bc +
                    shiftedReal.C.rowParity a.label b.label xy.fusion +
                    shiftedReal.C.rowParity (a.label + b.label) c.label abc) +
                  ((X.atom xy.left).shift + (X.atom xy.left).shift) +
                  ((Y.atom xy.right).shift + (Y.atom xy.right).shift) +
                  ((Z.atom qL.right).shift + (Z.atom qL.right).shift) := by
                ac_rfl
            _ = _ := by
              rw [zmod2_add_self, zmod2_add_self, zmod2_add_self,
                add_zero, add_zero, add_zero]
        rw [hgrade]
        exact memGrade_cast_symm shiftedReal.D hLabel _ _
          (realInvCoefficient_memGrade a.label b.label c.label
            bc a_bc xy.fusion abc)
      · have hX' :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              qL.left).left = qR.left := by simpa [xy] using hX
        have hY' :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              qL.left).right =
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                qR.right).left := by simpa [xy, yz] using hY
        have hZ' : qL.right ≠
            ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
              qR.right).right := by simpa [yz] using hZ
        unfold Associator.invEntry
        dsimp only
        rw [dif_pos hX', dif_pos hY', dif_neg hZ']
        exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0
    · have hX' :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            qL.left).left = qR.left := by simpa [xy] using hX
      have hY' :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            qL.left).right ≠
            ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
              qR.right).left := by simpa [xy, yz] using hY
      unfold Associator.invEntry
      dsimp only
      rw [dif_pos hX', dif_neg hY']
      exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0
  · have hX' :
        ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
          qL.left).left ≠ qR.left := by simpa [xy] using hX
    unfold Associator.invEntry
    dsimp only
    rw [dif_neg hX']
    exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0

/-! ## Evenness after endpoint normalization -/

/-- Multiplying a raw forward entry by its endpoint sign preserves its
categorical degree zero. -/
theorem realAssociatorHomEntry_even (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom.MemGrade 0 (RealAssociator.homEntry X Y Z qL qR) := by
  unfold RealAssociator.homEntry
  exact AtomHom.smul_memGrade realComputableShiftedRawDCT.laws.D _ _
    (realHomEntry_even X Y Z qL qR)

/-- The normalized inverse entry is even for the same reason. -/
theorem realAssociatorInvEntry_even (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom.MemGrade 0 (RealAssociator.invEntry X Y Z qR qL) := by
  unfold RealAssociator.invEntry
  exact AtomHom.smul_memGrade realComputableShiftedRawDCT.laws.D _ _
    (realInvEntry_even X Y Z qR qL)

/- The next two raw matrix lemmas remain available internally to consumers
that need to compare normalized and unnormalized coordinates. -/

private theorem rawAssociatorHom_even (X Y Z : Obj) :
    Hom.MemGrade 0 (Associator.hom shiftedReal X Y Z) := by
  intro i j
  exact realHomEntry_even X Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i)
    ((Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get j)

private theorem rawAssociatorInv_even (X Y Z : Obj) :
    Hom.MemGrade 0 (Associator.inv shiftedReal X Y Z) := by
  intro i j
  exact realInvEntry_even X Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i)
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get j)

/-- The executable endpoint-normalized forward associator is even. -/
theorem realAssociatorHom_even (X Y Z : Obj) :
    Hom.MemGrade 0 (RealAssociator.hom X Y Z) := by
  intro i j
  exact realAssociatorHomEntry_even X Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i)
    ((Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get j)

/-- The executable endpoint-normalized inverse associator is even. -/
theorem realAssociatorInv_even (X Y Z : Obj) :
    Hom.MemGrade 0 (RealAssociator.inv X Y Z) := by
  intro i j
  exact realAssociatorInvEntry_even X Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i)
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get j)

/-! ## Reindexing associator composites -/

/-- For the concrete shifted real coefficient family, one coefficient of an
arbitrary matrix composite is the ordinary finite sum over middle positions. -/
theorem realComp_coeff_as_sum {X Y Z : Obj}
    (f : Hom shiftedReal.D X Y) (g : Hom shiftedReal.D Y Z)
    (i : Fin X.size) (k : Fin Z.size)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra (X.atom i).label))]
    (hLabel : (X.atom i).label = (Z.atom k).label) :
    (Hom.comp f g i k).coeff hLabel =
      ∑ j : Fin Y.size, (AtomHom.comp (f i j) (g j k)).coeff hLabel := by
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  rw [Hom.comp, coeff_finSum realComputableShiftedRawDCT.laws.D]
  exact rawFinSum_eq_sum _ _

/-- A coefficient of the forward-then-inverse composite is the sum over
actual right-associated slots, rather than over positions in the slot list. -/
theorem realHomInv_comp_coeff_as_slot_sum (X Y Z : Obj)
    (i k : Fin (Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        ((Tensor.slots shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i)).label))]
    (hLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom i).label =
      ((Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom k).label) :
    (Hom.comp (Associator.hom shiftedReal X Y Z)
        (Associator.inv shiftedReal X Y Z) i k).coeff hLabel =
      ∑ qR : Tensor.Slot shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z),
        (AtomHom.comp
          (Associator.homEntry shiftedReal X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i) qR)
          (Associator.invEntry shiftedReal X Y Z qR
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get k))).coeff
          hLabel := by
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      ((Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom i).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  rw [Hom.comp,
    coeff_finSum realComputableShiftedRawDCT.laws.D]
  rw [rawFinSum_eq_sum]
  change (∑ j : Fin (Tensor.slots shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length,
      (AtomHom.comp
        (Associator.homEntry shiftedReal X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i)
          ((Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get j))
        (Associator.invEntry shiftedReal X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get j)
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get k))).coeff
        hLabel) = _
  simpa only [Associator.hom, Associator.inv, slotsEquiv_apply] using
    (slotsEquiv shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).sum_comp
        (fun qR =>
          (AtomHom.comp
            (Associator.homEntry shiftedReal X Y Z
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i) qR)
            (Associator.invEntry shiftedReal X Y Z qR
              ((Tensor.slots shiftedReal.D shiftedReal.C
                (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get k))).coeff
            hLabel)

/-- A coefficient of the inverse-then-forward composite is the sum over
actual left-associated slots. -/
theorem realInvHom_comp_coeff_as_slot_sum (X Y Z : Obj)
    (i k : Fin (Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        ((Tensor.slots shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i)).label))]
    (hLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).atom i).label =
      ((Tensor.obj shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).atom k).label) :
    (Hom.comp (Associator.inv shiftedReal X Y Z)
        (Associator.hom shiftedReal X Y Z) i k).coeff hLabel =
      ∑ qL : Tensor.Slot shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z,
        (AtomHom.comp
          (Associator.invEntry shiftedReal X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i) qL)
          (Associator.homEntry shiftedReal X Y Z qL
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get k))).coeff
          hLabel := by
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      ((Tensor.obj shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).atom i).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  rw [Hom.comp,
    coeff_finSum realComputableShiftedRawDCT.laws.D]
  rw [rawFinSum_eq_sum]
  change (∑ j : Fin (Tensor.slots shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length,
      (AtomHom.comp
        (Associator.invEntry shiftedReal X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i)
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get j))
        (Associator.homEntry shiftedReal X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get j)
          ((Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get k))).coeff
        hLabel) = _
  simpa only [Associator.hom, Associator.inv, slotsEquiv_apply] using
    (slotsEquiv shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).sum_comp
        (fun qL =>
          (AtomHom.comp
            (Associator.invEntry shiftedReal X Y Z
              ((Tensor.slots shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i) qL)
            (Associator.homEntry shiftedReal X Y Z qL
              ((Tensor.slots shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get k))).coeff
            hLabel)

/-! ### Vanishing away from the common three-object block -/

theorem realHomEntry_zero_of_left_ne (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (h : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).left ≠ qR.left) :
    Associator.homEntry shiftedReal X Y Z qL qR =
      AtomHom.zero shiftedReal.D _ _ := by
  unfold Associator.homEntry
  dsimp only
  rw [dif_neg h]

theorem realHomEntry_zero_of_middle_ne (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (h : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).right ≠
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          qR.right).left) :
    Associator.homEntry shiftedReal X Y Z qL qR =
      AtomHom.zero shiftedReal.D _ _ := by
  unfold Associator.homEntry
  dsimp only
  by_cases hX : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).left = qR.left
  · rw [dif_pos hX, dif_neg h]
  · rw [dif_neg hX]

theorem realHomEntry_zero_of_right_ne (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (h : qL.right ≠
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          qR.right).right) :
    Associator.homEntry shiftedReal X Y Z qL qR =
      AtomHom.zero shiftedReal.D _ _ := by
  unfold Associator.homEntry
  dsimp only
  by_cases hX : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).left = qR.left
  · rw [dif_pos hX]
    by_cases hY : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        qL.left).right =
          ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
            qR.right).left
    · rw [dif_pos hY, dif_neg h]
    · rw [dif_neg hY]
  · rw [dif_neg hX]

theorem realInvEntry_zero_of_left_ne (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (h : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).left ≠ qR.left) :
    Associator.invEntry shiftedReal X Y Z qR qL =
      AtomHom.zero shiftedReal.D _ _ := by
  unfold Associator.invEntry
  dsimp only
  rw [dif_neg h]

theorem realInvEntry_zero_of_middle_ne (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (h : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).right ≠
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          qR.right).left) :
    Associator.invEntry shiftedReal X Y Z qR qL =
      AtomHom.zero shiftedReal.D _ _ := by
  unfold Associator.invEntry
  dsimp only
  by_cases hX : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).left = qR.left
  · rw [dif_pos hX, dif_neg h]
  · rw [dif_neg hX]

theorem realInvEntry_zero_of_right_ne (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (h : qL.right ≠
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          qR.right).right) :
    Associator.invEntry shiftedReal X Y Z qR qL =
      AtomHom.zero shiftedReal.D _ _ := by
  unfold Associator.invEntry
  dsimp only
  by_cases hX : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      qL.left).left = qR.left
  · rw [dif_pos hX]
    by_cases hY : ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        qL.left).right =
          ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
            qR.right).left
    · rw [dif_pos hY, dif_neg h]
    · rw [dif_neg hY]
  · rw [dif_neg hX]

/-! ### Packed route slots on one fixed three-object block -/

def slotPosition (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Tensor.Slot dD dC X Y) :
    Fin (Tensor.slots dD dC X Y).length :=
  (slotsEquiv dD dC X Y).symm q

@[simp] theorem get_slotPosition (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Tensor.Slot dD dC X Y) :
    (Tensor.slots dD dC X Y).get (slotPosition dD dC X Y q) = q := by
  change slotsEquiv dD dC X Y
      ((slotsEquiv dD dC X Y).symm q) = q
  exact (slotsEquiv dD dC X Y).apply_symm_apply q

@[simp] theorem getElem_slotPosition (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Tensor.Slot dD dC X Y) :
    (Tensor.slots dD dC X Y)[(slotPosition dD dC X Y q).val] = q := by
  rw [← List.get_eq_getElem]
  exact get_slotPosition dD dC X Y q

def leftRouteSlot (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z := by
  let xy : Tensor.Slot shiftedReal.D shiftedReal.C X Y := ⟨i, j, ab⟩
  let p : Fin (Tensor.slots shiftedReal.D shiftedReal.C X Y).length :=
    slotPosition shiftedReal.D shiftedReal.C X Y xy
  have hp : (Tensor.slots shiftedReal.D shiftedReal.C X Y).get p = xy :=
    get_slotPosition shiftedReal.D shiftedReal.C X Y xy
  have hLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom p).label =
        (X.atom i).label + (Y.atom j).label := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get p)).label = _
    rw [hp]
    rfl
  exact ⟨p, k,
    Associator.castIndex shiftedReal hLabel.symm rfl abc⟩

def rightRouteSlot (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z) := by
  let yz : Tensor.Slot shiftedReal.D shiftedReal.C Y Z := ⟨j, k, bc⟩
  let p : Fin (Tensor.slots shiftedReal.D shiftedReal.C Y Z).length :=
    slotPosition shiftedReal.D shiftedReal.C Y Z yz
  have hp : (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get p = yz :=
    get_slotPosition shiftedReal.D shiftedReal.C Y Z yz
  have hLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom p).label =
        (Y.atom j).label + (Z.atom k).label := by
    change (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z
      ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get p)).label = _
    rw [hp]
    rfl
  exact ⟨i, p,
    Associator.castIndex shiftedReal rfl hLabel.symm a_bc⟩

@[simp] theorem leftRouteSlot_inner (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    (Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        (leftRouteSlot X Y Z i j k ab abc).left = ⟨i, j, ab⟩ :=
  by
    change (Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      (slotPosition shiftedReal.D shiftedReal.C X Y ⟨i, j, ab⟩) = _
    exact get_slotPosition shiftedReal.D shiftedReal.C X Y ⟨i, j, ab⟩

@[simp] theorem leftRouteSlot_right (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    (leftRouteSlot X Y Z i j k ab abc).right = k :=
  rfl

@[simp] theorem rightRouteSlot_left (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    (rightRouteSlot X Y Z i j k bc a_bc).left = i :=
  rfl

@[simp] theorem rightRouteSlot_inner (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
        (rightRouteSlot X Y Z i j k bc a_bc).right = ⟨j, k, bc⟩ :=
  by
    change (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
      (slotPosition shiftedReal.D shiftedReal.C Y Z ⟨j, k, bc⟩) = _
    exact get_slotPosition shiftedReal.D shiftedReal.C Y Z ⟨j, k, bc⟩

theorem leftRouteSlot_innerLabel (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom
      (leftRouteSlot X Y Z i j k ab abc).left).label =
        (X.atom i).label + (Y.atom j).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
    ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
      (leftRouteSlot X Y Z i j k ab abc).left)).label = _
  rw [leftRouteSlot_inner]
  rfl

theorem rightRouteSlot_innerLabel (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom
      (rightRouteSlot X Y Z i j k bc a_bc).right).label =
        (Y.atom j).label + (Z.atom k).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z
    ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
      (rightRouteSlot X Y Z i j k bc a_bc).right)).label = _
  rw [rightRouteSlot_inner]
  rfl

@[simp] theorem leftRouteSlot_outerRow (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    Associator.castIndex shiftedReal
      (leftRouteSlot_innerLabel X Y Z i j k ab abc) rfl
      (leftRouteSlot X Y Z i j k ab abc).fusion = abc := by
  unfold leftRouteSlot
  dsimp only [Tensor.Slot.fusion]
  exact castIndex_symm_cancel shiftedReal _ _ abc

@[simp] theorem rightRouteSlot_outerRow (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    Associator.castIndex shiftedReal rfl
      (rightRouteSlot_innerLabel X Y Z i j k bc a_bc)
      (rightRouteSlot X Y Z i j k bc a_bc).fusion = a_bc := by
  unfold rightRouteSlot
  dsimp only [Tensor.Slot.fusion]
  exact castIndex_symm_cancel shiftedReal _ _ a_bc

@[simp] theorem leftRouteSlot_label (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
      (leftRouteSlot X Y Z i j k ab abc)).label =
        (X.atom i).label + (Y.atom j).label + (Z.atom k).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        (leftRouteSlot X Y Z i j k ab abc).left)).label +
        (Z.atom (leftRouteSlot X Y Z i j k ab abc).right).label = _
  rw [leftRouteSlot_inner, leftRouteSlot_right]
  rfl

@[simp] theorem rightRouteSlot_label (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
      (rightRouteSlot X Y Z i j k bc a_bc)).label =
        (X.atom i).label + ((Y.atom j).label + (Z.atom k).label) := by
  change (X.atom (rightRouteSlot X Y Z i j k bc a_bc).left).label +
      (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          (rightRouteSlot X Y Z i j k bc a_bc).right)).label = _
  rw [rightRouteSlot_left, rightRouteSlot_inner]
  rfl

theorem routeAssocLabelEq (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
      (leftRouteSlot X Y Z i j k ab abc)).label =
    (Tensor.slotAtom shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
      (rightRouteSlot X Y Z i j k bc a_bc)).label := by
  rw [leftRouteSlot_label, rightRouteSlot_label]
  exact _root_.add_assoc _ _ _

/-! ### Agreement of packed and explicit route coordinates -/

/- Transporting the first endpoint of every row in a dependent slot tail
produces a heterogeneously equal tail.  This isolates the only dependent
transport needed to compare `leftSlotPack` with `leftRouteSlot`. -/
private theorem sigma_firstIndex_cast_heq (x : RawDCTData)
    {a a' : ZMod 8} (ha : a = a') {n : ℕ} (b : Fin n → ZMod 8)
    (k : Fin n) (r : x.C.Index a' (b k)) :
    (show (k : Fin n) × x.C.Index a (b k) from
      ⟨k, Associator.castIndex x ha.symm rfl r⟩) ≍
    (show (k : Fin n) × x.C.Index a' (b k) from ⟨k, r⟩) := by
  subst a'
  rfl

/- Applying the inverse right-slot packing equivalence and then unpacking
it leaves the stored outer fusion row unchanged up to dependent transport. -/
private theorem rightSlotPack_fusion_heq (X Y Z : Obj)
    (i : Fin X.size)
    (yz : Tensor.Slot shiftedReal.D shiftedReal.C Y Z)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z yz).label) :
    (rightSlotPack shiftedReal.D shiftedReal.C X Y Z
      ⟨i, yz, a_bc⟩).fusion ≍ a_bc := by
  let q : RightSlotCoordinates shiftedReal.D shiftedReal.C X Y Z :=
    ⟨i, yz, a_bc⟩
  let E : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z) ≃
        RightSlotCoordinates shiftedReal.D shiftedReal.C X Y Z :=
    Equiv.sigmaCongrRight fun i =>
      Equiv.sigmaCongr (slotsEquiv shiftedReal.D shiftedReal.C Y Z) fun j =>
        Equiv.refl (shiftedReal.C.Index (X.atom i).label
          ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom j).label)
  let qP := rightSlotPack shiftedReal.D shiftedReal.C X Y Z q
  have hback : E qP = q := by
    exact E.apply_symm_apply q
  have hsnd : (E qP).snd ≍ q.snd := (Sigma.ext_iff.mp hback).2
  have hsndEq : (E qP).snd = q.snd := eq_of_heq hsnd
  have hfusion : (E qP).snd.snd ≍ q.snd.snd :=
    (Sigma.ext_iff.mp hsndEq).2
  have hsame : (E qP).snd.snd ≍ qP.fusion := by
    rfl
  exact hsame.symm.trans hfusion

/-- Packing explicit right-route coordinates gives the canonical explicit
right route slot, including its transported outer fusion row. -/
theorem rightSlotPack_route (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    rightSlotPack shiftedReal.D shiftedReal.C X Y Z
        ⟨i, ⟨j, k, bc⟩, a_bc⟩ =
      rightRouteSlot X Y Z i j k bc a_bc := by
  let qP := rightSlotPack shiftedReal.D shiftedReal.C X Y Z
    ⟨i, (show Tensor.Slot shiftedReal.D shiftedReal.C Y Z from
      ⟨j, k, bc⟩), a_bc⟩
  let qR := rightRouteSlot X Y Z i j k bc a_bc
  have hleft : qP.left = qR.left := by
    simp [qP, qR]
  have hinner : qP.right = qR.right := by
    apply (slotsEquiv shiftedReal.D shiftedReal.C Y Z).injective
    rw [slotsEquiv_apply, slotsEquiv_apply]
    exact (rightSlotPack_inner shiftedReal.D shiftedReal.C X Y Z
      ⟨i, (show Tensor.Slot shiftedReal.D shiftedReal.C Y Z from
        ⟨j, k, bc⟩), a_bc⟩).trans
      (rightRouteSlot_inner X Y Z i j k bc a_bc).symm
  change qP = qR
  apply Sigma.ext hleft
  cases hleft
  apply heq_of_eq
  apply Sigma.ext hinner
  cases hinner
  apply heq_of_eq
  have hp := rightSlotPack_fusion_heq X Y Z i
    (show Tensor.Slot shiftedReal.D shiftedReal.C Y Z from ⟨j, k, bc⟩)
    a_bc
  have hr : qR.fusion ≍ a_bc := by
    unfold qR rightRouteSlot
    exact cast_heq _ _
  exact eq_of_heq (hp.trans hr.symm)

/-- Packing explicit left-route coordinates gives the canonical explicit
left route slot, including its transported outer fusion row. -/
theorem leftSlotPack_route (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    leftSlotPack shiftedReal.D shiftedReal.C X Y Z
        ⟨⟨i, j, ab⟩, k, abc⟩ =
      leftRouteSlot X Y Z i j k ab abc := by
  let xy : Tensor.Slot shiftedReal.D shiftedReal.C X Y := ⟨i, j, ab⟩
  let coord : LeftSlotCoordinates shiftedReal.D shiftedReal.C X Y Z :=
    ⟨xy, k, abc⟩
  let E : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z ≃
        LeftSlotCoordinates shiftedReal.D shiftedReal.C X Y Z :=
    Equiv.sigmaCongr (slotsEquiv shiftedReal.D shiftedReal.C X Y) fun i =>
      Equiv.refl ((k : Fin Z.size) ×
        shiftedReal.C.Index
          ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom i).label
          (Z.atom k).label)
  let qP := leftSlotPack shiftedReal.D shiftedReal.C X Y Z coord
  let qL := leftRouteSlot X Y Z i j k ab abc
  have hinner : qP.left = qL.left := by
    apply (slotsEquiv shiftedReal.D shiftedReal.C X Y).injective
    rw [slotsEquiv_apply, slotsEquiv_apply]
    exact (leftSlotPack_inner shiftedReal.D shiftedReal.C X Y Z coord).trans
      (leftRouteSlot_inner X Y Z i j k ab abc).symm
  have hback : E qP = coord := by
    exact E.apply_symm_apply coord
  have hpack : qP.snd ≍ coord.snd := by
    have hsnd : (E qP).snd ≍ coord.snd := (Sigma.ext_iff.mp hback).2
    have hsame : (E qP).snd ≍ qP.snd := by rfl
    exact hsame.symm.trans hsnd
  have hroute : qL.snd ≍ coord.snd := by
    let p : Fin (Tensor.slots shiftedReal.D shiftedReal.C X Y).length :=
      slotPosition shiftedReal.D shiftedReal.C X Y xy
    have hp : (Tensor.slots shiftedReal.D shiftedReal.C X Y).get p = xy :=
      get_slotPosition shiftedReal.D shiftedReal.C X Y xy
    have hLabel :
        ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom p).label =
          (X.atom i).label + (Y.atom j).label := by
      change (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y
        ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get p)).label = _
      rw [hp]
      rfl
    have hqL : qL =
        (show Tensor.Slot shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z from
          ⟨p, k, Associator.castIndex shiftedReal hLabel.symm rfl abc⟩) := by
      rfl
    rw [hqL]
    change (show (k : Fin Z.size) ×
        shiftedReal.C.Index
          ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom p).label
          (Z.atom k).label from
        ⟨k, Associator.castIndex shiftedReal hLabel.symm rfl abc⟩) ≍
      (show (k : Fin Z.size) ×
        shiftedReal.C.Index
          ((X.atom i).label + (Y.atom j).label) (Z.atom k).label from
        ⟨k, abc⟩)
    exact sigma_firstIndex_cast_heq shiftedReal hLabel
      (fun k => (Z.atom k).label) k abc
  change qP = qL
  apply Sigma.ext hinner
  exact hpack.trans hroute.symm

/-- Every left-associated nested slot is one explicit three-object route. -/
theorem exists_eq_leftRouteSlot (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    ∃ (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
      (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
      (abc : shiftedReal.C.Index
        ((X.atom i).label + (Y.atom j).label) (Z.atom k).label),
      qL = leftRouteSlot X Y Z i j k ab abc := by
  let q := (leftSlotPack shiftedReal.D shiftedReal.C X Y Z).symm qL
  have hrecover :
      leftSlotPack shiftedReal.D shiftedReal.C X Y Z q = qL :=
    (leftSlotPack shiftedReal.D shiftedReal.C X Y Z).apply_symm_apply qL
  rcases q with ⟨⟨i, j, ab⟩, k, abc⟩
  refine ⟨i, j, k, ab, abc, ?_⟩
  calc
    qL = leftSlotPack shiftedReal.D shiftedReal.C X Y Z
        ⟨⟨i, j, ab⟩, k, abc⟩ := hrecover.symm
    _ = leftRouteSlot X Y Z i j k ab abc :=
      leftSlotPack_route X Y Z i j k ab abc

/-- Every right-associated nested slot is one explicit three-object route. -/
theorem exists_eq_rightRouteSlot (X Y Z : Obj)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    ∃ (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
      (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
      (a_bc : shiftedReal.C.Index (X.atom i).label
        ((Y.atom j).label + (Z.atom k).label)),
      qR = rightRouteSlot X Y Z i j k bc a_bc := by
  let q := (rightSlotPack shiftedReal.D shiftedReal.C X Y Z).symm qR
  have hrecover :
      rightSlotPack shiftedReal.D shiftedReal.C X Y Z q = qR :=
    (rightSlotPack shiftedReal.D shiftedReal.C X Y Z).apply_symm_apply qR
  rcases q with ⟨i, ⟨j, k, bc⟩, a_bc⟩
  refine ⟨i, j, k, bc, a_bc, ?_⟩
  calc
    qR = rightSlotPack shiftedReal.D shiftedReal.C X Y Z
        ⟨i, ⟨j, k, bc⟩, a_bc⟩ := hrecover.symm
    _ = rightRouteSlot X Y Z i j k bc a_bc :=
      rightSlotPack_route X Y Z i j k bc a_bc

theorem realHomEntry_route_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    (Associator.homEntry shiftedReal X Y Z
      (leftRouteSlot X Y Z i j k ab abc)
      (rightRouteSlot X Y Z i j k bc a_bc)).coeff
        (routeAssocLabelEq X Y Z i j k ab abc bc a_bc) =
      cast
        (congrArg (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          (leftRouteSlot_label X Y Z i j k ab abc).symm)
        (Associator.homCoefficient shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          ab abc bc a_bc) := by
  let qL := leftRouteSlot X Y Z i j k ab abc
  let qR := rightRouteSlot X Y Z i j k bc a_bc
  let xy := (Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left
  let yz := (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right
  have hxy : xy = ⟨i, j, ab⟩ := by
    simpa only [xy, qL] using leftRouteSlot_inner X Y Z i j k ab abc
  have hyz : yz = ⟨j, k, bc⟩ := by
    simpa only [yz, qR] using rightRouteSlot_inner X Y Z i j k bc a_bc
  have hqLRight : qL.right = k := by
    simpa only [qL] using leftRouteSlot_right X Y Z i j k ab abc
  have hqRLeft : qR.left = i := by
    simpa only [qR] using rightRouteSlot_left X Y Z i j k bc a_bc
  have hX : xy.left = qR.left := by
    rw [hxy, hqRLeft]
    rfl
  have hY : xy.right = yz.left := by
    rw [hxy, hyz]
    rfl
  have hZ : qL.right = yz.right := by
    rw [hqLRight, hyz]
    rfl
  let a := X.atom xy.left
  let b := Y.atom xy.right
  let c := Z.atom qL.right
  have hBCLeft : (Y.atom yz.left).label = b.label := by
    simpa only [b] using congrArg (fun t => (Y.atom t).label) hY.symm
  have hBCRight : (Z.atom yz.right).label = c.label := by
    simpa only [c] using congrArg (fun t => (Z.atom t).label) hZ.symm
  let bc' : shiftedReal.C.Index b.label c.label :=
    Associator.castIndex shiftedReal hBCLeft hBCRight yz.fusion
  have hALeft : (X.atom qR.left).label = a.label := by
    simpa only [a] using congrArg (fun t => (X.atom t).label) hX.symm
  have hYZLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom qR.right).label =
        b.label + c.label := by
    change (Y.atom yz.left).label + (Z.atom yz.right).label = _
    rw [hBCLeft, hBCRight]
  let a_bc' : shiftedReal.C.Index a.label (b.label + c.label) :=
    Associator.castIndex shiftedReal hALeft hYZLabel qR.fusion
  have hXYLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom qL.left).label =
        a.label + b.label := by
    rfl
  let abc' : shiftedReal.C.Index (a.label + b.label) c.label :=
    Associator.castIndex shiftedReal hXYLabel rfl qL.fusion
  have hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR).label := by
    change ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom qL.left).label +
          (Z.atom qL.right).label =
      (X.atom qR.left).label +
        ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom qR.right).label
    rw [hXYLabel, hYZLabel, hALeft]
    exact _root_.add_assoc _ _ _
  rw [show Associator.homEntry shiftedReal X Y Z qL qR =
      AtomHom.ofLabelEq hLabel
        (Associator.homCoefficient shiftedReal a.label b.label c.label
          xy.fusion abc' bc' a_bc') by
    simp only [Associator.homEntry, xy, yz, hX, hY, hZ, dite_true]
    rfl]
  rw [AtomHom.coeff_ofLabelEq]
  have ha : a.label = (X.atom i).label := by
    simpa only [a, Tensor.Slot.left] using
      congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
        (X.atom s.left).label) hxy
  have hb : b.label = (Y.atom j).label := by
    simpa only [b, Tensor.Slot.right] using
      congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
        (Y.atom s.right).label) hxy
  have hc : c.label = (Z.atom k).label := by
    simpa only [c] using congrArg (fun t => (Z.atom t).label) hqLRight
  have hha : ha =
      congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
        (X.atom s.left).label) hxy := by
    apply Subsingleton.elim
  have hhb : hb =
      congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
        (Y.atom s.right).label) hxy := by
    apply Subsingleton.elim
  have hab : Associator.castIndex shiftedReal ha hb xy.fusion = ab := by
    calc
      _ = Associator.castIndex shiftedReal
          (congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
            (X.atom s.left).label) hxy)
          (congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
            (Y.atom s.right).label) hxy) xy.fusion :=
        castIndex_proof_irrel shiftedReal _ _ _ _ xy.fusion
      _ = ab := by
        simpa only [Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion] using
          slotFusion_cast_of_eq shiftedReal X Y xy ⟨i, j, ab⟩ hxy
  have habc : Associator.castIndex shiftedReal
      (congrArg₂ (· + ·) ha hb) hc abc' = abc := by
    calc
      _ = Associator.castIndex shiftedReal
          (leftRouteSlot_innerLabel X Y Z i j k ab abc) rfl qL.fusion := by
        unfold abc'
        rw [castIndex_trans]
        rfl
      _ = abc := by
        simpa only [qL] using
          leftRouteSlot_outerRow X Y Z i j k ab abc
  have hbc : Associator.castIndex shiftedReal hb hc bc' = bc := by
    unfold bc'
    rw [castIndex_trans]
    simpa only [Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion] using
      slotFusion_cast_of_eq shiftedReal Y Z yz ⟨j, k, bc⟩ hyz
  have ha_bc : Associator.castIndex shiftedReal ha
      (congrArg₂ (· + ·) hb hc) a_bc' = a_bc := by
    calc
      _ = Associator.castIndex shiftedReal rfl
          (rightRouteSlot_innerLabel X Y Z i j k bc a_bc) qR.fusion := by
        unfold a_bc'
        rw [castIndex_trans]
        rfl
      _ = a_bc := by
        simpa only [qR] using
          rightRouteSlot_outerRow X Y Z i j k bc a_bc
  calc
    Associator.homCoefficient shiftedReal a.label b.label c.label
        xy.fusion abc' bc' a_bc' =
      cast
        (congrArg
          (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          (congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc)).symm
        (Associator.homCoefficient shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          (Associator.castIndex shiftedReal ha hb xy.fusion)
          (Associator.castIndex shiftedReal
            (congrArg₂ (· + ·) ha hb) hc abc')
          (Associator.castIndex shiftedReal hb hc bc')
          (Associator.castIndex shiftedReal ha
            (congrArg₂ (· + ·) hb hc) a_bc')) :=
      homCoefficient_transport shiftedReal ha hb hc
        xy.fusion abc' bc' a_bc'
    _ = _ := by
      rw [hab, habc, hbc, ha_bc]
      have hpath :
          congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc =
            leftRouteSlot_label X Y Z i j k ab abc := by
        apply Subsingleton.elim
      rw [hpath]
      exact cast_congrArg_symm
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
        (leftRouteSlot_label X Y Z i j k ab abc)
        (Associator.homCoefficient shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          ab abc bc a_bc)

/- On a compatible pair of ternary routes, the inverse matrix entry is the
stored inverse connector coefficient, transported back to the source label. -/
theorem realInvEntry_route_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (bc : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (a_bc : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    (Associator.invEntry shiftedReal X Y Z
      (rightRouteSlot X Y Z i j k bc a_bc)
      (leftRouteSlot X Y Z i j k ab abc)).coeff
        (routeAssocLabelEq X Y Z i j k ab abc bc a_bc).symm =
      cast
        (congrArg (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
          ((leftRouteSlot_label X Y Z i j k ab abc).symm.trans
            (routeAssocLabelEq X Y Z i j k ab abc bc a_bc)))
        (Associator.invCoefficient shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          bc a_bc ab abc) := by
  let qL := leftRouteSlot X Y Z i j k ab abc
  let qR := rightRouteSlot X Y Z i j k bc a_bc
  let xy := (Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left
  let yz := (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right
  have hxy : xy = ⟨i, j, ab⟩ := by
    simpa only [xy, qL] using leftRouteSlot_inner X Y Z i j k ab abc
  have hyz : yz = ⟨j, k, bc⟩ := by
    simpa only [yz, qR] using rightRouteSlot_inner X Y Z i j k bc a_bc
  have hqLRight : qL.right = k := by
    simpa only [qL] using leftRouteSlot_right X Y Z i j k ab abc
  have hqRLeft : qR.left = i := by
    simpa only [qR] using rightRouteSlot_left X Y Z i j k bc a_bc
  have hX : xy.left = qR.left := by
    rw [hxy, hqRLeft]
    rfl
  have hY : xy.right = yz.left := by
    rw [hxy, hyz]
    rfl
  have hZ : qL.right = yz.right := by
    rw [hqLRight, hyz]
    rfl
  let a := X.atom xy.left
  let b := Y.atom xy.right
  let c := Z.atom qL.right
  have hBCLeft : (Y.atom yz.left).label = b.label := by
    simpa only [b] using congrArg (fun t => (Y.atom t).label) hY.symm
  have hBCRight : (Z.atom yz.right).label = c.label := by
    simpa only [c] using congrArg (fun t => (Z.atom t).label) hZ.symm
  let bc' : shiftedReal.C.Index b.label c.label :=
    Associator.castIndex shiftedReal hBCLeft hBCRight yz.fusion
  have hALeft : (X.atom qR.left).label = a.label := by
    simpa only [a] using congrArg (fun t => (X.atom t).label) hX.symm
  have hYZLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom qR.right).label =
        b.label + c.label := by
    change (Y.atom yz.left).label + (Z.atom yz.right).label = _
    rw [hBCLeft, hBCRight]
  let a_bc' : shiftedReal.C.Index a.label (b.label + c.label) :=
    Associator.castIndex shiftedReal hALeft hYZLabel qR.fusion
  have hXYLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom qL.left).label =
        a.label + b.label := by
    rfl
  let abc' : shiftedReal.C.Index (a.label + b.label) c.label :=
    Associator.castIndex shiftedReal hXYLabel rfl qL.fusion
  have hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qR).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qL).label := by
    change (X.atom qR.left).label +
          ((Tensor.obj shiftedReal.D shiftedReal.C Y Z).atom qR.right).label =
      ((Tensor.obj shiftedReal.D shiftedReal.C X Y).atom qL.left).label +
        (Z.atom qL.right).label
    rw [hXYLabel, hYZLabel, hALeft]
    exact (_root_.add_assoc _ _ _).symm
  rw [show Associator.invEntry shiftedReal X Y Z qR qL =
      AtomHom.ofLabelEq hLabel
        (cast
          (congrArg
            (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
            hLabel).symm
          (Associator.invCoefficient shiftedReal a.label b.label c.label
            bc' a_bc' xy.fusion abc')) by
    simp only [Associator.invEntry, xy, yz, hX, hY, hZ, dite_true]
    rfl]
  rw [AtomHom.coeff_ofLabelEq]
  have ha : a.label = (X.atom i).label := by
    simpa only [a, Tensor.Slot.left] using
      congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
        (X.atom s.left).label) hxy
  have hb : b.label = (Y.atom j).label := by
    simpa only [b, Tensor.Slot.right] using
      congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
        (Y.atom s.right).label) hxy
  have hc : c.label = (Z.atom k).label := by
    simpa only [c] using congrArg (fun t => (Z.atom t).label) hqLRight
  have hab : Associator.castIndex shiftedReal ha hb xy.fusion = ab := by
    calc
      _ = Associator.castIndex shiftedReal
          (congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
            (X.atom s.left).label) hxy)
          (congrArg (fun s : Tensor.Slot shiftedReal.D shiftedReal.C X Y =>
            (Y.atom s.right).label) hxy) xy.fusion :=
        castIndex_proof_irrel shiftedReal _ _ _ _ xy.fusion
      _ = ab := by
        simpa only [Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion] using
          slotFusion_cast_of_eq shiftedReal X Y xy ⟨i, j, ab⟩ hxy
  have habc : Associator.castIndex shiftedReal
      (congrArg₂ (· + ·) ha hb) hc abc' = abc := by
    calc
      _ = Associator.castIndex shiftedReal
          (leftRouteSlot_innerLabel X Y Z i j k ab abc) rfl qL.fusion := by
        unfold abc'
        rw [castIndex_trans]
        rfl
      _ = abc := by
        simpa only [qL] using
          leftRouteSlot_outerRow X Y Z i j k ab abc
  have hbc : Associator.castIndex shiftedReal hb hc bc' = bc := by
    unfold bc'
    rw [castIndex_trans]
    simpa only [Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion] using
      slotFusion_cast_of_eq shiftedReal Y Z yz ⟨j, k, bc⟩ hyz
  have ha_bc : Associator.castIndex shiftedReal ha
      (congrArg₂ (· + ·) hb hc) a_bc' = a_bc := by
    calc
      _ = Associator.castIndex shiftedReal rfl
          (rightRouteSlot_innerLabel X Y Z i j k bc a_bc) qR.fusion := by
        unfold a_bc'
        rw [castIndex_trans]
        rfl
      _ = a_bc := by
        simpa only [qR] using
          rightRouteSlot_outerRow X Y Z i j k bc a_bc
  let F := fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier
  let htotal := congrArg₂ (· + ·) (congrArg₂ (· + ·) ha hb) hc
  let explicitInv := Associator.invCoefficient shiftedReal
    (X.atom i).label (Y.atom j).label (Z.atom k).label bc a_bc ab abc
  calc
    cast (congrArg F hLabel).symm
        (Associator.invCoefficient shiftedReal a.label b.label c.label
          bc' a_bc' xy.fusion abc') =
      cast (congrArg F hLabel).symm
        (cast (congrArg F htotal).symm
          (Associator.invCoefficient shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            (Associator.castIndex shiftedReal hb hc bc')
            (Associator.castIndex shiftedReal ha
              (congrArg₂ (· + ·) hb hc) a_bc')
            (Associator.castIndex shiftedReal ha hb xy.fusion)
            (Associator.castIndex shiftedReal
              (congrArg₂ (· + ·) ha hb) hc abc'))) := by
        exact congrArg
          (fun t => cast (congrArg F hLabel).symm t)
          (invCoefficient_transport shiftedReal ha hb hc
            bc' a_bc' xy.fusion abc')
    _ = cast (congrArg F hLabel).symm
        (cast (congrArg F htotal).symm explicitInv) := by
      rw [hbc, ha_bc, hab, habc]
    _ = cast (congrArg F (hLabel.trans htotal)).symm explicitInv :=
      cast_congrArg_symm_trans F hLabel htotal explicitInv
    _ = _ := by
      apply cast_proof_irrel

/-! ## Inverse identities from the stored connector matrix laws -/

/- One compatible middle route contributes the transported product of its
inverse and forward raw connector coefficients. -/
private theorem realHomInv_route_comp_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceAB targetAB :
      shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC targetABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (middleBC : shiftedReal.C.Index
      (Y.atom j).label (Z.atom k).label)
    (middleABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label)) :
    let qLS := leftRouteSlot X Y Z i j k sourceAB sourceABC
    let qLT := leftRouteSlot X Y Z i j k targetAB targetABC
    let qR := rightRouteSlot X Y Z i j k middleBC middleABC
    let hS := routeAssocLabelEq X Y Z i j k
      sourceAB sourceABC middleBC middleABC
    let hT := (routeAssocLabelEq X Y Z i j k
      targetAB targetABC middleBC middleABC).symm
    (AtomHom.comp
      (Associator.homEntry shiftedReal X Y Z qLS qR)
      (Associator.invEntry shiftedReal X Y Z qR qLT)).coeff
        (hS.trans hT) =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).symm)
        ((shiftedReal.D.algebra
          ((X.atom i).label + (Y.atom j).label + (Z.atom k).label)).mul
          (Associator.invCoefficient shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            middleBC middleABC targetAB targetABC)
          (Associator.homCoefficient shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            sourceAB sourceABC middleBC middleABC)) := by
  dsimp only
  rw [AtomHom.coeff_comp
    (Associator.homEntry shiftedReal X Y Z
      (leftRouteSlot X Y Z i j k sourceAB sourceABC)
      (rightRouteSlot X Y Z i j k middleBC middleABC))
    (Associator.invEntry shiftedReal X Y Z
      (rightRouteSlot X Y Z i j k middleBC middleABC)
      (leftRouteSlot X Y Z i j k targetAB targetABC))
    (routeAssocLabelEq X Y Z i j k
      sourceAB sourceABC middleBC middleABC)
    (routeAssocLabelEq X Y Z i j k
      targetAB targetABC middleBC middleABC).symm]
  rw [realHomEntry_route_coeff, realInvEntry_route_coeff]
  let F := fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier
  let total :=
    (X.atom i).label + (Y.atom j).label + (Z.atom k).label
  let sourceLabel :=
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
      (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label
  let hSource : sourceLabel = total :=
    leftRouteSlot_label X Y Z i j k sourceAB sourceABC
  let targetLabel :=
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
      (leftRouteSlot X Y Z i j k targetAB targetABC)).label
  let rightLabel :=
    (Tensor.slotAtom shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
      (rightRouteSlot X Y Z i j k middleBC middleABC)).label
  let hTarget : targetLabel = total :=
    leftRouteSlot_label X Y Z i j k targetAB targetABC
  let hSR : sourceLabel = rightLabel :=
    routeAssocLabelEq X Y Z i j k
      sourceAB sourceABC middleBC middleABC
  let hTR : targetLabel = rightLabel :=
    routeAssocLabelEq X Y Z i j k
      targetAB targetABC middleBC middleABC
  let invC := Associator.invCoefficient shiftedReal
    (X.atom i).label (Y.atom j).label (Z.atom k).label
    middleBC middleABC targetAB targetABC
  let homC := Associator.homCoefficient shiftedReal
    (X.atom i).label (Y.atom j).label (Z.atom k).label
    sourceAB sourceABC middleBC middleABC
  change (shiftedReal.D.algebra sourceLabel).mul
      (cast (congrArg F hSR).symm
        (cast (congrArg F (hTarget.symm.trans hTR)) invC))
      (cast (congrArg F hSource).symm homC) =
    cast (congrArg F hSource).symm
      ((shiftedReal.D.algebra total).mul invC homC)
  have hInv :
      cast (congrArg F hSR).symm
          (cast (congrArg F (hTarget.symm.trans hTR)) invC) =
        cast (congrArg F hSource).symm invC := by
    rw [cast_cast_eq]
  rw [hInv]
  exact (cast_algebra_mul_of_label_eq shiftedReal.D hSource.symm
    (congrArg F hSource).symm invC homC).symm

/- Summing the compatible right-associated middle routes is exactly the
stored inverse-times-forward connector matrix identity. -/
private theorem realHomInv_route_sum (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceAB targetAB :
      shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC targetABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label))] :
    let qLS := leftRouteSlot X Y Z i j k sourceAB sourceABC
    let qLT := leftRouteSlot X Y Z i j k targetAB targetABC
    let hST := (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).trans
      (leftRouteSlot_label X Y Z i j k targetAB targetABC).symm
    ∑ qR : Tensor.Slot shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z),
      (AtomHom.comp
        (Associator.homEntry shiftedReal X Y Z qLS qR)
        (Associator.invEntry shiftedReal X Y Z qR qLT)).coeff hST =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).symm)
        (Associator.leftDelta shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          sourceAB sourceABC targetAB targetABC) := by
  dsimp only
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      ((X.atom i).label + (Y.atom j).label + (Z.atom k).label))) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  let F := fun qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z) =>
    (AtomHom.comp
      (Associator.homEntry shiftedReal X Y Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC) qR)
      (Associator.invEntry shiftedReal X Y Z qR
        (leftRouteSlot X Y Z i j k targetAB targetABC))).coeff
      ((leftRouteSlot_label X Y Z i j k sourceAB sourceABC).trans
        (leftRouteSlot_label X Y Z i j k targetAB targetABC).symm)
  rw [sum_rightSlotCoordinates X Y Z F]
  change (∑ i0 : Fin X.size,
      ∑ yz : Tensor.Slot shiftedReal.D shiftedReal.C Y Z,
      ∑ a_bc : shiftedReal.C.Index (X.atom i0).label
          (Tensor.slotAtom shiftedReal.D shiftedReal.C Y Z yz).label,
        F (rightSlotPack shiftedReal.D shiftedReal.C X Y Z
          ⟨i0, yz, a_bc⟩)) = _
  calc
    _ = ∑ i0 : Fin X.size, ∑ j0 : Fin Y.size,
        ∑ k0 : Fin Z.size,
        ∑ bc : shiftedReal.C.Index
          (Y.atom j0).label (Z.atom k0).label,
        ∑ a_bc : shiftedReal.C.Index (X.atom i0).label
          ((Y.atom j0).label + (Z.atom k0).label),
          F (rightRouteSlot X Y Z i0 j0 k0 bc a_bc) := by
      apply Finset.sum_congr rfl
      intro i0 _
      rw [sum_slots Y Z]
      simp_rw [rightSlotPack_route]
      rfl
    _ = ∑ j0 : Fin Y.size, ∑ k0 : Fin Z.size,
        ∑ bc : shiftedReal.C.Index
          (Y.atom j0).label (Z.atom k0).label,
        ∑ a_bc : shiftedReal.C.Index (X.atom i).label
          ((Y.atom j0).label + (Z.atom k0).label),
          F (rightRouteSlot X Y Z i j0 k0 bc a_bc) := by
      apply Finset.sum_eq_single i
      · intro i0 _ hi0
        apply Finset.sum_eq_zero
        intro j0 _
        apply Finset.sum_eq_zero
        intro k0 _
        apply Finset.sum_eq_zero
        intro bc _
        apply Finset.sum_eq_zero
        intro a_bc _
        unfold F
        have hne :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).left ≠
              (rightRouteSlot X Y Z i0 j0 k0 bc a_bc).left := by
          intro h
          have hl :
              ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
                (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).left = i :=
            congrArg Sigma.fst
              (leftRouteSlot_inner X Y Z i j k sourceAB sourceABC)
          have hr : (rightRouteSlot X Y Z i0 j0 k0 bc a_bc).left = i0 :=
            rightRouteSlot_left X Y Z i0 j0 k0 bc a_bc
          exact (Ne.symm hi0) (hl.symm.trans (h.trans hr))
        rw [realHomEntry_zero_of_left_ne X Y Z _ _ hne]
        rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        exact AtomHom.coeff_zero _
      · simp
    _ = ∑ k0 : Fin Z.size,
        ∑ bc : shiftedReal.C.Index
          (Y.atom j).label (Z.atom k0).label,
        ∑ a_bc : shiftedReal.C.Index (X.atom i).label
          ((Y.atom j).label + (Z.atom k0).label),
          F (rightRouteSlot X Y Z i j k0 bc a_bc) := by
      apply Finset.sum_eq_single j
      · intro j0 _ hj0
        apply Finset.sum_eq_zero
        intro k0 _
        apply Finset.sum_eq_zero
        intro bc _
        apply Finset.sum_eq_zero
        intro a_bc _
        unfold F
        have hne :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).right ≠
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                (rightRouteSlot X Y Z i j0 k0 bc a_bc).right).left := by
          intro h
          have hl :
              ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
                (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).right = j :=
            congrArg (fun s => s.right)
              (leftRouteSlot_inner X Y Z i j k sourceAB sourceABC)
          have hr :
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                (rightRouteSlot X Y Z i j0 k0 bc a_bc).right).left = j0 :=
            congrArg Sigma.fst
              (rightRouteSlot_inner X Y Z i j0 k0 bc a_bc)
          exact (Ne.symm hj0) (hl.symm.trans (h.trans hr))
        rw [realHomEntry_zero_of_middle_ne X Y Z _ _ hne]
        rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        exact AtomHom.coeff_zero _
      · simp
    _ = ∑ bc : shiftedReal.C.Index
          (Y.atom j).label (Z.atom k).label,
        ∑ a_bc : shiftedReal.C.Index (X.atom i).label
          ((Y.atom j).label + (Z.atom k).label),
          F (rightRouteSlot X Y Z i j k bc a_bc) := by
      apply Finset.sum_eq_single k
      · intro k0 _ hk0
        apply Finset.sum_eq_zero
        intro bc _
        apply Finset.sum_eq_zero
        intro a_bc _
        unfold F
        have hne :
            (leftRouteSlot X Y Z i j k sourceAB sourceABC).right ≠
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                (rightRouteSlot X Y Z i j k0 bc a_bc).right).right := by
          intro h
          have hl :
              (leftRouteSlot X Y Z i j k sourceAB sourceABC).right = k :=
            leftRouteSlot_right X Y Z i j k sourceAB sourceABC
          have hr :
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                (rightRouteSlot X Y Z i j k0 bc a_bc).right).right = k0 :=
            congrArg (fun s => s.right)
              (rightRouteSlot_inner X Y Z i j k0 bc a_bc)
          exact (Ne.symm hk0) (hl.symm.trans (h.trans hr))
        rw [realHomEntry_zero_of_right_ne X Y Z _ _ hne]
        rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        exact AtomHom.coeff_zero _
      · simp
    _ = _ := by
      unfold F
      simp_rw [realHomInv_route_comp_coeff]
      let total :=
        (X.atom i).label + (Y.atom j).label + (Z.atom k).label
      let hSource :
          (Tensor.slotAtom shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
            (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label = total := by
        simpa only [total] using
          leftRouteSlot_label X Y Z i j k sourceAB sourceABC
      let hCast := congrArg
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
        hSource.symm
      have hmatrix := Associator.inv_homCoefficient_matrix_identity
        shiftedReal realComputableShiftedRawDCT.laws
        (X.atom i).label (Y.atom j).label (Z.atom k).label
        sourceAB targetAB sourceABC targetABC
      have hcast := congrArg (fun u => cast hCast u) hmatrix
      rw [cast_rawFinSum shiftedReal.D hSource.symm] at hcast
      rw [rawFinSum_congr _ (fun middleBC =>
        cast_rawFinSum shiftedReal.D hSource.symm (fun middleABC =>
          (shiftedReal.D.algebra total).mul
            (Associator.invCoefficient shiftedReal
              (X.atom i).label (Y.atom j).label (Z.atom k).label
              middleBC middleABC targetAB targetABC)
            (Associator.homCoefficient shiftedReal
              (X.atom i).label (Y.atom j).label (Z.atom k).label
              sourceAB sourceABC middleBC middleABC)))] at hcast
      simpa only [rawFinSum_eq_sum] using hcast

/- Canonical matrix positions of explicit left-associated routes let the
coordinate identity be compared with the categorical identity matrix. -/
def leftRoutePosition (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    Fin (Tensor.obj shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).size :=
  slotPosition shiftedReal.D shiftedReal.C
    (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
    (leftRouteSlot X Y Z i j k ab abc)

theorem leftRoutePosition_label (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (ab : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (abc : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    ((Tensor.obj shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom
        (leftRoutePosition X Y Z i j k ab abc)).label =
      (X.atom i).label + (Y.atom j).label + (Z.atom k).label := by
  change (Tensor.slotAtom shiftedReal.D shiftedReal.C
    (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
    ((Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get
      (leftRoutePosition X Y Z i j k ab abc))).label = _
  unfold leftRoutePosition
  rw [get_slotPosition]
  exact leftRouteSlot_label X Y Z i j k ab abc

private theorem leftRoute_id_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceAB targetAB :
      shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC targetABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label))]
    (hLabel :
      ((Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom
          (leftRoutePosition X Y Z i j k sourceAB sourceABC)).label =
      ((Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom
          (leftRoutePosition X Y Z i j k targetAB targetABC)).label) :
    (Hom.id shiftedReal.D
      (Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
      (leftRoutePosition X Y Z i j k sourceAB sourceABC)
      (leftRoutePosition X Y Z i j k targetAB targetABC)).coeff hLabel =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          (leftRoutePosition_label X Y Z i j k sourceAB sourceABC).symm)
        (Associator.leftDelta shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          sourceAB sourceABC targetAB targetABC) := by
  classical
  let qS := leftRouteSlot X Y Z i j k sourceAB sourceABC
  let qT := leftRouteSlot X Y Z i j k targetAB targetABC
  let pS := leftRoutePosition X Y Z i j k sourceAB sourceABC
  let pT := leftRoutePosition X Y Z i j k targetAB targetABC
  by_cases hAB : targetAB = sourceAB
  · subst targetAB
    by_cases hABC : targetABC = sourceABC
    · subst targetABC
      change (Hom.id shiftedReal.D
        (Tensor.obj shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) pS pS).coeff
          hLabel = _
      have hid : Hom.id shiftedReal.D
          (Tensor.obj shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) pS pS =
        AtomHom.id shiftedReal.D
          ((Tensor.obj shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom pS) := by
        simp [Hom.id]
      rw [hid]
      rw [show hLabel = rfl by apply Subsingleton.elim]
      rw [AtomHom.coeff_id, Associator.leftDelta_source]
      exact (cast_algebra_one_of_label_eq shiftedReal.D
        (leftRoutePosition_label X Y Z i j k sourceAB sourceABC).symm _).symm
    · have hRoute : qS ≠ qT := by
        intro h
        have hpack :
            leftSlotPack shiftedReal.D shiftedReal.C X Y Z
                ⟨⟨i, j, sourceAB⟩, k, sourceABC⟩ =
              leftSlotPack shiftedReal.D shiftedReal.C X Y Z
                ⟨⟨i, j, sourceAB⟩, k, targetABC⟩ := by
          rw [leftSlotPack_route, leftSlotPack_route]
          exact h
        have hcoord :=
          (leftSlotPack shiftedReal.D shiftedReal.C X Y Z).injective hpack
        have : sourceABC = targetABC := by
          simp only [Sigma.mk.inj_iff, heq_iff_eq, true_and] at hcoord
          change sourceABC = targetABC at hcoord
          exact hcoord
        exact hABC this.symm
      have hPos : pS ≠ pT := by
        intro h
        unfold pS pT leftRoutePosition slotPosition at h
        exact hRoute
          ((slotsEquiv shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).symm.injective h)
      change (Hom.id shiftedReal.D
        (Tensor.obj shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) pS pT).coeff
          hLabel = _
      have hid : Hom.id shiftedReal.D
          (Tensor.obj shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) pS pT =
        AtomHom.zero shiftedReal.D
          ((Tensor.obj shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom pS)
          ((Tensor.obj shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom pT) := by
        simp [Hom.id, hPos]
      rw [hid, AtomHom.coeff_zero]
      rw [Associator.leftDelta_off_second shiftedReal
        (X.atom i).label (Y.atom j).label (Z.atom k).label
        sourceAB sourceABC targetABC hABC]
      exact (cast_algebra_zero_of_label_eq shiftedReal.D
        (leftRoutePosition_label X Y Z i j k sourceAB sourceABC).symm _).symm
  · have hRoute : qS ≠ qT := by
      intro h
      have hinner := congrArg
        (fun q => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get q.left) h
      have : sourceAB = targetAB := by
        simpa only [qS, qT, leftRouteSlot_inner, Sigma.mk.inj_iff,
          heq_iff_eq, true_and] using hinner
      exact hAB this.symm
    have hPos : pS ≠ pT := by
      intro h
      unfold pS pT leftRoutePosition slotPosition at h
      exact hRoute
        ((slotsEquiv shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).symm.injective h)
    change (Hom.id shiftedReal.D
      (Tensor.obj shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) pS pT).coeff
        hLabel = _
    have hid : Hom.id shiftedReal.D
        (Tensor.obj shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) pS pT =
      AtomHom.zero shiftedReal.D
        ((Tensor.obj shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom pS)
        ((Tensor.obj shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).atom pT) := by
      simp [Hom.id, hPos]
    rw [hid, AtomHom.coeff_zero]
    rw [Associator.leftDelta_off_first shiftedReal
      (X.atom i).label (Y.atom j).label (Z.atom k).label
      sourceAB targetAB sourceABC targetABC hAB]
    exact (cast_algebra_zero_of_label_eq shiftedReal.D
      (leftRoutePosition_label X Y Z i j k sourceAB sourceABC).symm _).symm

/- Outside a common atomic triple, one of the two associator entries in every
middle summand vanishes. -/
private theorem realHomInv_route_sum_zero_of_left_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceAB : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : shiftedReal.C.Index (X.atom i').label (Y.atom j').label)
    (targetABC : shiftedReal.C.Index
      ((X.atom i').label + (Y.atom j').label) (Z.atom k').label)
    (hi : i' ≠ i)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i' j' k' targetAB targetABC)).label) :
    ∑ qR : Tensor.Slot shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z),
      (AtomHom.comp
        (Associator.homEntry shiftedReal X Y Z
          (leftRouteSlot X Y Z i j k sourceAB sourceABC) qR)
        (Associator.invEntry shiftedReal X Y Z qR
          (leftRouteSlot X Y Z i' j' k' targetAB targetABC))).coeff hLabel = 0 := by
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  apply Finset.sum_eq_zero
  intro qR _
  by_cases hcompat :
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).left = qR.left
  · have htarget :
        ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
          (leftRouteSlot X Y Z i' j' k' targetAB targetABC).left).left ≠
            qR.left := by
      intro h
      have hs :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).left = i :=
        congrArg Sigma.fst
          (leftRouteSlot_inner X Y Z i j k sourceAB sourceABC)
      have ht :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            (leftRouteSlot X Y Z i' j' k' targetAB targetABC).left).left = i' :=
        congrArg Sigma.fst
          (leftRouteSlot_inner X Y Z i' j' k' targetAB targetABC)
      exact hi (ht.symm.trans (h.trans (hcompat.symm.trans hs)))
    rw [realInvEntry_zero_of_left_ne X Y Z qR _ htarget]
    rw [AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _
  · rw [realHomEntry_zero_of_left_ne X Y Z _ qR hcompat]
    rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _

private theorem realHomInv_route_sum_zero_of_middle_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceAB : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : shiftedReal.C.Index (X.atom i').label (Y.atom j').label)
    (targetABC : shiftedReal.C.Index
      ((X.atom i').label + (Y.atom j').label) (Z.atom k').label)
    (hj : j' ≠ j)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i' j' k' targetAB targetABC)).label) :
    ∑ qR : Tensor.Slot shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z),
      (AtomHom.comp
        (Associator.homEntry shiftedReal X Y Z
          (leftRouteSlot X Y Z i j k sourceAB sourceABC) qR)
        (Associator.invEntry shiftedReal X Y Z qR
          (leftRouteSlot X Y Z i' j' k' targetAB targetABC))).coeff hLabel = 0 := by
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  apply Finset.sum_eq_zero
  intro qR _
  by_cases hcompat :
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
        (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).right =
      ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right).left
  · have htarget :
        ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
          (leftRouteSlot X Y Z i' j' k' targetAB targetABC).left).right ≠
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right).left := by
      intro h
      have hs :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            (leftRouteSlot X Y Z i j k sourceAB sourceABC).left).right = j :=
        congrArg (fun s => s.right)
          (leftRouteSlot_inner X Y Z i j k sourceAB sourceABC)
      have ht :
          ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
            (leftRouteSlot X Y Z i' j' k' targetAB targetABC).left).right = j' :=
        congrArg (fun s => s.right)
          (leftRouteSlot_inner X Y Z i' j' k' targetAB targetABC)
      exact hj (ht.symm.trans (h.trans (hcompat.symm.trans hs)))
    rw [realInvEntry_zero_of_middle_ne X Y Z qR _ htarget]
    rw [AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _
  · rw [realHomEntry_zero_of_middle_ne X Y Z _ qR hcompat]
    rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _

private theorem realHomInv_route_sum_zero_of_right_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceAB : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : shiftedReal.C.Index (X.atom i').label (Y.atom j').label)
    (targetABC : shiftedReal.C.Index
      ((X.atom i').label + (Y.atom j').label) (Z.atom k').label)
    (hk : k' ≠ k)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i' j' k' targetAB targetABC)).label) :
    ∑ qR : Tensor.Slot shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z),
      (AtomHom.comp
        (Associator.homEntry shiftedReal X Y Z
          (leftRouteSlot X Y Z i j k sourceAB sourceABC) qR)
        (Associator.invEntry shiftedReal X Y Z qR
          (leftRouteSlot X Y Z i' j' k' targetAB targetABC))).coeff hLabel = 0 := by
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  apply Finset.sum_eq_zero
  intro qR _
  by_cases hcompat :
      (leftRouteSlot X Y Z i j k sourceAB sourceABC).right =
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right).right
  · have htarget :
        (leftRouteSlot X Y Z i' j' k' targetAB targetABC).right ≠
          ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get qR.right).right := by
      intro h
      have hs : (leftRouteSlot X Y Z i j k sourceAB sourceABC).right = k :=
        leftRouteSlot_right X Y Z i j k sourceAB sourceABC
      have ht : (leftRouteSlot X Y Z i' j' k' targetAB targetABC).right = k' :=
        leftRouteSlot_right X Y Z i' j' k' targetAB targetABC
      exact hk (ht.symm.trans (h.trans (hcompat.symm.trans hs)))
    rw [realInvEntry_zero_of_right_ne X Y Z qR _ htarget]
    rw [AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _
  · rw [realHomEntry_zero_of_right_ne X Y Z _ qR hcompat]
    rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _


/-! ## Endpoint signs in the two composite orders -/

private theorem endpointSign_mul_self (X Y Z : Obj)
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    RealAssociator.endpointSign X Y Z qL *
        RealAssociator.endpointSign X Y Z qL = 1 := by
  unfold RealAssociator.endpointSign
  exact shiftParitySign_mul_self _

private theorem correctedHomInv_term (X Y Z : Obj)
    (qLS qLT : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z)
    (qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom.comp (RealAssociator.homEntry X Y Z qLS qR)
        (RealAssociator.invEntry X Y Z qR qLT) =
      AtomHom.smul
        (RealAssociator.endpointSign X Y Z qLS *
          RealAssociator.endpointSign X Y Z qLT)
        (AtomHom.comp (Associator.homEntry shiftedReal X Y Z qLS qR)
          (Associator.invEntry shiftedReal X Y Z qR qLT)) := by
  unfold RealAssociator.homEntry RealAssociator.invEntry
  rw [AtomHom.smul_comp realComputableShiftedRawDCT.laws.D]
  rw [AtomHom.comp_smul realComputableShiftedRawDCT.laws.D]
  exact (AtomHom.mul_smul realComputableShiftedRawDCT.laws.D _ _ _).symm

private theorem correctedInvHom_term (X Y Z : Obj)
    (qRS qRT : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z))
    (qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom.comp (RealAssociator.invEntry X Y Z qRS qL)
        (RealAssociator.homEntry X Y Z qL qRT) =
      AtomHom.comp (Associator.invEntry shiftedReal X Y Z qRS qL)
        (Associator.homEntry shiftedReal X Y Z qL qRT) := by
  unfold RealAssociator.invEntry RealAssociator.homEntry
  rw [AtomHom.smul_comp realComputableShiftedRawDCT.laws.D]
  rw [AtomHom.comp_smul realComputableShiftedRawDCT.laws.D]
  rw [← AtomHom.mul_smul realComputableShiftedRawDCT.laws.D]
  rw [endpointSign_mul_self]
  exact AtomHom.one_smul realComputableShiftedRawDCT.laws.D _


/-! ## Left-slot identity for the normalized forward composite -/

private def leftSlotDelta (X Y Z : Obj)
    (qS qT : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qS)
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qT) :=
  if h : qS = qT then
    h ▸ AtomHom.id shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z qS)
  else AtomHom.zero shiftedReal.D _ _

private theorem leftRouteSlot_ne_of_left_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceAB : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : shiftedReal.C.Index (X.atom i').label (Y.atom j').label)
    (targetABC : shiftedReal.C.Index
      ((X.atom i').label + (Y.atom j').label) (Z.atom k').label)
    (hi : i' ≠ i) :
    leftRouteSlot X Y Z i j k sourceAB sourceABC ≠
      leftRouteSlot X Y Z i' j' k' targetAB targetABC := by
  intro hroute
  have hinner := congrArg
    (fun q => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get q.left)
    hroute
  have hinnerI := congrArg Sigma.fst hinner
  have hsI := congrArg Sigma.fst
    (leftRouteSlot_inner X Y Z i j k sourceAB sourceABC)
  have htI := congrArg Sigma.fst
    (leftRouteSlot_inner X Y Z i' j' k' targetAB targetABC)
  exact hi (htI.symm.trans (hinnerI.symm.trans hsI))

private theorem leftRouteSlot_ne_of_middle_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceAB : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : shiftedReal.C.Index (X.atom i').label (Y.atom j').label)
    (targetABC : shiftedReal.C.Index
      ((X.atom i').label + (Y.atom j').label) (Z.atom k').label)
    (hj : j' ≠ j) :
    leftRouteSlot X Y Z i j k sourceAB sourceABC ≠
      leftRouteSlot X Y Z i' j' k' targetAB targetABC := by
  intro hroute
  have hinner := congrArg
    (fun q => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get q.left)
    hroute
  have hinnerJ := congrArg (fun q => q.right) hinner
  have hsJ := congrArg (fun q => q.right)
    (leftRouteSlot_inner X Y Z i j k sourceAB sourceABC)
  have htJ := congrArg (fun q => q.right)
    (leftRouteSlot_inner X Y Z i' j' k' targetAB targetABC)
  exact hj (htJ.symm.trans (hinnerJ.symm.trans hsJ))

private theorem leftRouteSlot_ne_of_right_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceAB : shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    (targetAB : shiftedReal.C.Index (X.atom i').label (Y.atom j').label)
    (targetABC : shiftedReal.C.Index
      ((X.atom i').label + (Y.atom j').label) (Z.atom k').label)
    (hk : k' ≠ k) :
    leftRouteSlot X Y Z i j k sourceAB sourceABC ≠
      leftRouteSlot X Y Z i' j' k' targetAB targetABC := by
  intro hroute
  have hright := congrArg (fun q => q.right) hroute
  have hsR := leftRouteSlot_right X Y Z i j k sourceAB sourceABC
  have htR := leftRouteSlot_right X Y Z i' j' k' targetAB targetABC
  exact hk (htR.symm.trans (hright.symm.trans hsR))

private theorem leftRoute_delta_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceAB targetAB :
      shiftedReal.C.Index (X.atom i).label (Y.atom j).label)
    (sourceABC targetABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k targetAB targetABC)).label) :
    (leftSlotDelta X Y Z
      (leftRouteSlot X Y Z i j k sourceAB sourceABC)
      (leftRouteSlot X Y Z i j k targetAB targetABC)).coeff hLabel =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).symm)
        (Associator.leftDelta shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          sourceAB sourceABC targetAB targetABC) := by
  classical
  by_cases hAB : targetAB = sourceAB
  · subst targetAB
    by_cases hABC : targetABC = sourceABC
    · subst targetABC
      unfold leftSlotDelta
      rw [dif_pos rfl]
      rw [show hLabel = rfl by apply Subsingleton.elim]
      rw [AtomHom.coeff_id, Associator.leftDelta_source]
      exact (cast_algebra_one_of_label_eq shiftedReal.D
        (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).symm _).symm
    · have hRoute :
          leftRouteSlot X Y Z i j k sourceAB sourceABC ≠
            leftRouteSlot X Y Z i j k sourceAB targetABC := by
        intro h
        have hpack :
            leftSlotPack shiftedReal.D shiftedReal.C X Y Z
                ⟨⟨i, j, sourceAB⟩, k, sourceABC⟩ =
              leftSlotPack shiftedReal.D shiftedReal.C X Y Z
                ⟨⟨i, j, sourceAB⟩, k, targetABC⟩ := by
          rw [leftSlotPack_route, leftSlotPack_route]
          exact h
        have hcoord :=
          (leftSlotPack shiftedReal.D shiftedReal.C X Y Z).injective hpack
        have : sourceABC = targetABC := by
          simp only [Sigma.mk.inj_iff, heq_iff_eq, true_and] at hcoord
          change sourceABC = targetABC at hcoord
          exact hcoord
        exact hABC this.symm
      unfold leftSlotDelta
      rw [dif_neg hRoute, AtomHom.coeff_zero]
      rw [Associator.leftDelta_off_second shiftedReal
        (X.atom i).label (Y.atom j).label (Z.atom k).label
        sourceAB sourceABC targetABC hABC]
      exact (cast_algebra_zero_of_label_eq shiftedReal.D
        (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).symm _).symm
  · have hRoute :
        leftRouteSlot X Y Z i j k sourceAB sourceABC ≠
          leftRouteSlot X Y Z i j k targetAB targetABC := by
      intro h
      have hinner := congrArg
        (fun q => (Tensor.slots shiftedReal.D shiftedReal.C X Y).get q.left) h
      have : sourceAB = targetAB := by
        simpa only [leftRouteSlot_inner, Sigma.mk.inj_iff,
          heq_iff_eq, true_and] using hinner
      exact hAB this.symm
    unfold leftSlotDelta
    rw [dif_neg hRoute, AtomHom.coeff_zero]
    rw [Associator.leftDelta_off_first shiftedReal
      (X.atom i).label (Y.atom j).label (Z.atom k).label
      sourceAB targetAB sourceABC targetABC hAB]
    exact (cast_algebra_zero_of_label_eq shiftedReal.D
      (leftRouteSlot_label X Y Z i j k sourceAB sourceABC).symm _).symm

private theorem rawHomInv_slot_entry (X Y Z : Obj)
    (qS qT : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length
        (fun m => AtomHom.comp
          (Associator.homEntry shiftedReal X Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m))
          (Associator.invEntry shiftedReal X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m) qT)) =
      leftSlotDelta X Y Z qS qT := by
  classical
  rcases exists_eq_leftRouteSlot X Y Z qS with
    ⟨i, j, k, sourceAB, sourceABC, hqS⟩
  rcases exists_eq_leftRouteSlot X Y Z qT with
    ⟨i', j', k', targetAB, targetABC, hqT⟩
  subst qS
  subst qT
  apply AtomHom.ext
  intro hLabel
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC)).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  rw [coeff_finSum realComputableShiftedRawDCT.laws.D]
  rw [rawFinSum_eq_sum]
  let F := fun qR : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z) =>
    (AtomHom.comp
      (Associator.homEntry shiftedReal X Y Z
        (leftRouteSlot X Y Z i j k sourceAB sourceABC) qR)
      (Associator.invEntry shiftedReal X Y Z qR
        (leftRouteSlot X Y Z i' j' k' targetAB targetABC))).coeff hLabel
  change (∑ m : Fin (Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length,
        F ((Tensor.slots shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m)) = _
  rw [show (∑ m : Fin (Tensor.slots shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length,
        F ((Tensor.slots shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m)) =
      ∑ qR, F qR by
    simpa only [slotsEquiv_apply] using
      (slotsEquiv shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).sum_comp F]
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      by_cases hk : k' = k
      · subst k'
        calc
          _ = cast
              (congrArg (fun t : ZMod 8 =>
                (shiftedReal.D.algebra t).carrier)
                (leftRouteSlot_label X Y Z i j k
                  sourceAB sourceABC).symm)
              (Associator.leftDelta shiftedReal
                (X.atom i).label (Y.atom j).label (Z.atom k).label
                sourceAB sourceABC targetAB targetABC) :=
            realHomInv_route_sum X Y Z i j k sourceAB targetAB
              sourceABC targetABC
          _ = _ := (leftRoute_delta_coeff X Y Z i j k
            sourceAB targetAB sourceABC targetABC hLabel).symm
      · rw [realHomInv_route_sum_zero_of_right_ne X Y Z
          i j k i j k' sourceAB sourceABC targetAB targetABC hk hLabel]
        unfold leftSlotDelta
        rw [dif_neg (leftRouteSlot_ne_of_right_ne X Y Z
          i j k i j k' sourceAB sourceABC targetAB targetABC hk)]
        exact (AtomHom.coeff_zero hLabel).symm
    · rw [realHomInv_route_sum_zero_of_middle_ne X Y Z
        i j k i j' k' sourceAB sourceABC targetAB targetABC hj hLabel]
      unfold leftSlotDelta
      rw [dif_neg (leftRouteSlot_ne_of_middle_ne X Y Z
        i j k i j' k' sourceAB sourceABC targetAB targetABC hj)]
      exact (AtomHom.coeff_zero hLabel).symm
  · rw [realHomInv_route_sum_zero_of_left_ne X Y Z
      i j k i' j' k' sourceAB sourceABC targetAB targetABC hi hLabel]
    unfold leftSlotDelta
    rw [dif_neg (leftRouteSlot_ne_of_left_ne X Y Z
      i j k i' j' k' sourceAB sourceABC targetAB targetABC hi)]
    exact (AtomHom.coeff_zero hLabel).symm

private theorem correctedHomInv_slot_entry (X Y Z : Obj)
    (qS qT : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) :
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length
        (fun m => AtomHom.comp
          (RealAssociator.homEntry X Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m))
          (RealAssociator.invEntry X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C X
              (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m) qT)) =
      leftSlotDelta X Y Z qS qT := by
  let s := RealAssociator.endpointSign X Y Z qS *
    RealAssociator.endpointSign X Y Z qT
  calc
    _ = AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length
        (fun m => AtomHom.smul s
          (AtomHom.comp
            (Associator.homEntry shiftedReal X Y Z qS
              ((Tensor.slots shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m))
            (Associator.invEntry shiftedReal X Y Z
              ((Tensor.slots shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m) qT))) := by
      apply AtomHom.finSum_congr
      intro m
      exact correctedHomInv_term X Y Z qS qT _
    _ = AtomHom.smul s
        (AtomHom.finSum
          (Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length
          (fun m => AtomHom.comp
            (Associator.homEntry shiftedReal X Y Z qS
              ((Tensor.slots shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m))
            (Associator.invEntry shiftedReal X Y Z
              ((Tensor.slots shiftedReal.D shiftedReal.C X
                (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m) qT))) :=
      AtomHom.finSum_smul realComputableShiftedRawDCT.laws.D s _
    _ = AtomHom.smul s (leftSlotDelta X Y Z qS qT) := by
      rw [rawHomInv_slot_entry]
    _ = _ := by
      unfold s leftSlotDelta
      by_cases h : qS = qT
      · subst qT
        rw [dif_pos rfl, endpointSign_mul_self]
        exact AtomHom.one_smul realComputableShiftedRawDCT.laws.D _
      · rw [dif_neg h]
        exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

theorem realAssociator_hom_inv (X Y Z : Obj) :
    Hom.comp (RealAssociator.hom X Y Z) (RealAssociator.inv X Y Z) =
      Hom.id shiftedReal.D
        (Tensor.obj shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z) := by
  apply Hom.ext
  intro i k
  let qS := (Tensor.slots shiftedReal.D shiftedReal.C
    (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get i
  let qT := (Tensor.slots shiftedReal.D shiftedReal.C
    (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get k
  unfold Hom.comp RealAssociator.hom RealAssociator.inv
  change AtomHom.finSum
      (Tensor.slots shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).length
      (fun m => AtomHom.comp
        (RealAssociator.homEntry X Y Z qS
          ((Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m))
        (RealAssociator.invEntry X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get m) qT)) = _
  rw [correctedHomInv_slot_entry X Y Z qS qT]
  by_cases hik : i = k
  · subst k
    simp only [qS, qT, leftSlotDelta, dif_pos, Hom.id]
    rfl
  · have hq : qS ≠ qT := by
      intro h
      apply hik
      exact (slotsEquiv shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).injective
        (by simpa only [slotsEquiv_apply, qS, qT] using h)
    rw [leftSlotDelta, dif_neg hq]
    simp only [Hom.id, dif_neg hik]
    rfl

/-! ## Right-slot identity for the normalized backward composite -/

private theorem realInvHom_route_comp_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceBC targetBC :
      shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC targetABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (middleAB : shiftedReal.C.Index
      (X.atom i).label (Y.atom j).label)
    (middleABC : shiftedReal.C.Index
      ((X.atom i).label + (Y.atom j).label) (Z.atom k).label) :
    let qRS := rightRouteSlot X Y Z i j k sourceBC sourceABC
    let qRT := rightRouteSlot X Y Z i j k targetBC targetABC
    let qL := leftRouteSlot X Y Z i j k middleAB middleABC
    let hS := (routeAssocLabelEq X Y Z i j k
      middleAB middleABC sourceBC sourceABC).symm
    let hT := routeAssocLabelEq X Y Z i j k
      middleAB middleABC targetBC targetABC
    (AtomHom.comp
      (Associator.invEntry shiftedReal X Y Z qRS qL)
      (Associator.homEntry shiftedReal X Y Z qL qRT)).coeff
        (hS.trans hT) =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          ((rightRouteSlot_label X Y Z i j k
            sourceBC sourceABC).trans
            (_root_.add_assoc (X.atom i).label
              (Y.atom j).label (Z.atom k).label).symm).symm)
        ((shiftedReal.D.algebra
          ((X.atom i).label + (Y.atom j).label + (Z.atom k).label)).mul
          (Associator.homCoefficient shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            middleAB middleABC targetBC targetABC)
          (Associator.invCoefficient shiftedReal
            (X.atom i).label (Y.atom j).label (Z.atom k).label
            sourceBC sourceABC middleAB middleABC)) := by
  dsimp only
  rw [AtomHom.coeff_comp
    (Associator.invEntry shiftedReal X Y Z
      (rightRouteSlot X Y Z i j k sourceBC sourceABC)
      (leftRouteSlot X Y Z i j k middleAB middleABC))
    (Associator.homEntry shiftedReal X Y Z
      (leftRouteSlot X Y Z i j k middleAB middleABC)
      (rightRouteSlot X Y Z i j k targetBC targetABC))
    (routeAssocLabelEq X Y Z i j k
      middleAB middleABC sourceBC sourceABC).symm
    (routeAssocLabelEq X Y Z i j k
      middleAB middleABC targetBC targetABC)]
  rw [realInvEntry_route_coeff, realHomEntry_route_coeff]
  let F := fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier
  let total :=
    (X.atom i).label + (Y.atom j).label + (Z.atom k).label
  let sourceLabel :=
    (Tensor.slotAtom shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
      (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label
  let middleLabel :=
    (Tensor.slotAtom shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z
      (leftRouteSlot X Y Z i j k middleAB middleABC)).label
  let targetLabel :=
    (Tensor.slotAtom shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
      (rightRouteSlot X Y Z i j k targetBC targetABC)).label
  let hMiddle : middleLabel = total :=
    leftRouteSlot_label X Y Z i j k middleAB middleABC
  let hSource : sourceLabel = total :=
    (rightRouteSlot_label X Y Z i j k sourceBC sourceABC).trans
      (_root_.add_assoc (X.atom i).label
        (Y.atom j).label (Z.atom k).label).symm
  let hSL : sourceLabel = middleLabel :=
    (routeAssocLabelEq X Y Z i j k
      middleAB middleABC sourceBC sourceABC).symm
  let hLT : middleLabel = targetLabel :=
    routeAssocLabelEq X Y Z i j k
      middleAB middleABC targetBC targetABC
  let homC := Associator.homCoefficient shiftedReal
    (X.atom i).label (Y.atom j).label (Z.atom k).label
    middleAB middleABC targetBC targetABC
  let invC := Associator.invCoefficient shiftedReal
    (X.atom i).label (Y.atom j).label (Z.atom k).label
    sourceBC sourceABC middleAB middleABC
  change (shiftedReal.D.algebra sourceLabel).mul
      (cast (congrArg F hSL).symm
        (cast (congrArg F hMiddle).symm homC))
      (cast (congrArg F (hMiddle.symm.trans hSL.symm)) invC) =
    cast (congrArg F hSource).symm
      ((shiftedReal.D.algebra total).mul homC invC)
  have hHom :
      cast (congrArg F hSL).symm
          (cast (congrArg F hMiddle).symm homC) =
        cast (congrArg F hSource).symm homC := by
    rw [cast_cast_eq]
  have hInv :
      cast (congrArg F (hMiddle.symm.trans hSL.symm)) invC =
        cast (congrArg F hSource).symm invC := by
    apply cast_proof_irrel
  rw [hHom, hInv]
  exact (cast_algebra_mul_of_label_eq shiftedReal.D hSource.symm
    (congrArg F hSource).symm homC invC).symm

private theorem realInvHom_route_sum (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceBC targetBC :
      shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC targetABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label))] :
    let qRS := rightRouteSlot X Y Z i j k sourceBC sourceABC
    let qRT := rightRouteSlot X Y Z i j k targetBC targetABC
    let hST := (rightRouteSlot_label X Y Z i j k sourceBC sourceABC).trans
      (rightRouteSlot_label X Y Z i j k targetBC targetABC).symm
    ∑ qL : Tensor.Slot shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z,
      (AtomHom.comp
        (Associator.invEntry shiftedReal X Y Z qRS qL)
        (Associator.homEntry shiftedReal X Y Z qL qRT)).coeff hST =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          ((rightRouteSlot_label X Y Z i j k sourceBC sourceABC).trans
            (_root_.add_assoc (X.atom i).label
              (Y.atom j).label (Z.atom k).label).symm).symm)
        (Associator.rightDelta shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          sourceBC sourceABC targetBC targetABC) := by
  dsimp only
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      ((X.atom i).label + (Y.atom j).label + (Z.atom k).label))) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  let F := fun qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z =>
    (AtomHom.comp
      (Associator.invEntry shiftedReal X Y Z
        (rightRouteSlot X Y Z i j k sourceBC sourceABC) qL)
      (Associator.homEntry shiftedReal X Y Z qL
        (rightRouteSlot X Y Z i j k targetBC targetABC))).coeff
      ((rightRouteSlot_label X Y Z i j k sourceBC sourceABC).trans
        (rightRouteSlot_label X Y Z i j k targetBC targetABC).symm)
  rw [sum_leftSlotCoordinates X Y Z F]
  change (∑ xy : Tensor.Slot shiftedReal.D shiftedReal.C X Y,
      ∑ k0 : Fin Z.size,
      ∑ abc : shiftedReal.C.Index
          (Tensor.slotAtom shiftedReal.D shiftedReal.C X Y xy).label
          (Z.atom k0).label,
        F (leftSlotPack shiftedReal.D shiftedReal.C X Y Z
          ⟨xy, k0, abc⟩)) = _
  calc
    _ = ∑ i0 : Fin X.size, ∑ j0 : Fin Y.size,
        ∑ ab : shiftedReal.C.Index
          (X.atom i0).label (Y.atom j0).label,
        ∑ k0 : Fin Z.size,
        ∑ abc : shiftedReal.C.Index
          ((X.atom i0).label + (Y.atom j0).label) (Z.atom k0).label,
          F (leftRouteSlot X Y Z i0 j0 k0 ab abc) := by
      rw [sum_slots X Y]
      simp_rw [leftSlotPack_route]
      rfl
    _ = ∑ j0 : Fin Y.size,
        ∑ ab : shiftedReal.C.Index
          (X.atom i).label (Y.atom j0).label,
        ∑ k0 : Fin Z.size,
        ∑ abc : shiftedReal.C.Index
          ((X.atom i).label + (Y.atom j0).label) (Z.atom k0).label,
          F (leftRouteSlot X Y Z i j0 k0 ab abc) := by
      apply Finset.sum_eq_single i
      · intro i0 _ hi0
        apply Finset.sum_eq_zero
        intro j0 _
        apply Finset.sum_eq_zero
        intro ab _
        apply Finset.sum_eq_zero
        intro k0 _
        apply Finset.sum_eq_zero
        intro abc _
        unfold F
        have hne :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              (leftRouteSlot X Y Z i0 j0 k0 ab abc).left).left ≠
              (rightRouteSlot X Y Z i j k sourceBC sourceABC).left := by
          rw [leftRouteSlot_inner, rightRouteSlot_left]
          exact hi0
        rw [realInvEntry_zero_of_left_ne X Y Z _ _ hne]
        rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        exact AtomHom.coeff_zero _
      · simp
    _ = ∑ ab : shiftedReal.C.Index
          (X.atom i).label (Y.atom j).label,
        ∑ k0 : Fin Z.size,
        ∑ abc : shiftedReal.C.Index
          ((X.atom i).label + (Y.atom j).label) (Z.atom k0).label,
          F (leftRouteSlot X Y Z i j k0 ab abc) := by
      apply Finset.sum_eq_single j
      · intro j0 _ hj0
        apply Finset.sum_eq_zero
        intro ab _
        apply Finset.sum_eq_zero
        intro k0 _
        apply Finset.sum_eq_zero
        intro abc _
        unfold F
        have hne :
            ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get
              (leftRouteSlot X Y Z i j0 k0 ab abc).left).right ≠
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                (rightRouteSlot X Y Z i j k sourceBC sourceABC).right).left := by
          rw [leftRouteSlot_inner, rightRouteSlot_inner]
          exact hj0
        rw [realInvEntry_zero_of_middle_ne X Y Z _ _ hne]
        rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        exact AtomHom.coeff_zero _
      · simp
    _ = ∑ ab : shiftedReal.C.Index
          (X.atom i).label (Y.atom j).label,
        ∑ abc : shiftedReal.C.Index
          ((X.atom i).label + (Y.atom j).label) (Z.atom k).label,
          F (leftRouteSlot X Y Z i j k ab abc) := by
      apply Finset.sum_congr rfl
      intro ab _
      apply Finset.sum_eq_single k
      · intro k0 _ hk0
        apply Finset.sum_eq_zero
        intro abc _
        unfold F
        have hne :
            (leftRouteSlot X Y Z i j k0 ab abc).right ≠
              ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
                (rightRouteSlot X Y Z i j k sourceBC sourceABC).right).right := by
          rw [leftRouteSlot_right, rightRouteSlot_inner]
          exact hk0
        rw [realInvEntry_zero_of_right_ne X Y Z _ _ hne]
        rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
        exact AtomHom.coeff_zero _
      · simp
    _ = _ := by
      unfold F
      simp_rw [realInvHom_route_comp_coeff]
      let total :=
        (X.atom i).label + (Y.atom j).label + (Z.atom k).label
      let hSource :
          (Tensor.slotAtom shiftedReal.D shiftedReal.C X
            (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
            (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label = total :=
        (rightRouteSlot_label X Y Z i j k sourceBC sourceABC).trans
          (_root_.add_assoc (X.atom i).label
            (Y.atom j).label (Z.atom k).label).symm
      let hCast := congrArg
        (fun t : ZMod 8 => (shiftedReal.D.algebra t).carrier)
        hSource.symm
      have hmatrix := Associator.hom_invCoefficient_matrix_identity
        shiftedReal realComputableShiftedRawDCT.laws
        (X.atom i).label (Y.atom j).label (Z.atom k).label
        sourceBC targetBC sourceABC targetABC
      have hcast := congrArg (fun u => cast hCast u) hmatrix
      rw [cast_rawFinSum shiftedReal.D hSource.symm] at hcast
      rw [rawFinSum_congr _ (fun middleAB =>
        cast_rawFinSum shiftedReal.D hSource.symm (fun middleABC =>
          (shiftedReal.D.algebra total).mul
            (Associator.homCoefficient shiftedReal
              (X.atom i).label (Y.atom j).label (Z.atom k).label
              middleAB middleABC targetBC targetABC)
            (Associator.invCoefficient shiftedReal
              (X.atom i).label (Y.atom j).label (Z.atom k).label
              sourceBC sourceABC middleAB middleABC)))] at hcast
      simpa only [rawFinSum_eq_sum] using hcast

private def rightSlotDelta (X Y Z : Obj)
    (qS qT : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qS)
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qT) :=
  if h : qS = qT then
    h ▸ AtomHom.id shiftedReal.D
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z) qS)
  else AtomHom.zero shiftedReal.D _ _

private theorem rightRouteSlot_ne_of_left_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceBC : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (targetBC : shiftedReal.C.Index (Y.atom j').label (Z.atom k').label)
    (targetABC : shiftedReal.C.Index (X.atom i').label
      ((Y.atom j').label + (Z.atom k').label))
    (hi : i' ≠ i) :
    rightRouteSlot X Y Z i j k sourceBC sourceABC ≠
      rightRouteSlot X Y Z i' j' k' targetBC targetABC := by
  intro hroute
  have hleft := congrArg (fun q => q.left) hroute
  rw [rightRouteSlot_left, rightRouteSlot_left] at hleft
  exact hi hleft.symm

private theorem rightRouteSlot_ne_of_middle_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceBC : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (targetBC : shiftedReal.C.Index (Y.atom j').label (Z.atom k').label)
    (targetABC : shiftedReal.C.Index (X.atom i').label
      ((Y.atom j').label + (Z.atom k').label))
    (hj : j' ≠ j) :
    rightRouteSlot X Y Z i j k sourceBC sourceABC ≠
      rightRouteSlot X Y Z i' j' k' targetBC targetABC := by
  intro hroute
  have hinner := congrArg
    (fun q => (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get q.right)
    hroute
  have hinnerJ := congrArg Sigma.fst hinner
  have hsJ := congrArg Sigma.fst
    (rightRouteSlot_inner X Y Z i j k sourceBC sourceABC)
  have htJ := congrArg Sigma.fst
    (rightRouteSlot_inner X Y Z i' j' k' targetBC targetABC)
  exact hj (htJ.symm.trans (hinnerJ.symm.trans hsJ))

private theorem rightRouteSlot_ne_of_right_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceBC : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (targetBC : shiftedReal.C.Index (Y.atom j').label (Z.atom k').label)
    (targetABC : shiftedReal.C.Index (X.atom i').label
      ((Y.atom j').label + (Z.atom k').label))
    (hk : k' ≠ k) :
    rightRouteSlot X Y Z i j k sourceBC sourceABC ≠
      rightRouteSlot X Y Z i' j' k' targetBC targetABC := by
  intro hroute
  have hinner := congrArg
    (fun q => (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get q.right)
    hroute
  have hinnerK := congrArg (fun q => q.right) hinner
  have hsK := congrArg (fun q => q.right)
    (rightRouteSlot_inner X Y Z i j k sourceBC sourceABC)
  have htK := congrArg (fun q => q.right)
    (rightRouteSlot_inner X Y Z i' j' k' targetBC targetABC)
  exact hk (htK.symm.trans (hinnerK.symm.trans hsK))

private theorem rightRoute_delta_coeff (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (sourceBC targetBC :
      shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC targetABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k targetBC targetABC)).label) :
    (rightSlotDelta X Y Z
      (rightRouteSlot X Y Z i j k sourceBC sourceABC)
      (rightRouteSlot X Y Z i j k targetBC targetABC)).coeff hLabel =
      cast
        (congrArg (fun t : ZMod 8 =>
          (shiftedReal.D.algebra t).carrier)
          ((rightRouteSlot_label X Y Z i j k sourceBC sourceABC).trans
            (_root_.add_assoc (X.atom i).label
              (Y.atom j).label (Z.atom k).label).symm).symm)
        (Associator.rightDelta shiftedReal
          (X.atom i).label (Y.atom j).label (Z.atom k).label
          sourceBC sourceABC targetBC targetABC) := by
  classical
  let hSource := (rightRouteSlot_label X Y Z i j k
    sourceBC sourceABC).trans
      (_root_.add_assoc (X.atom i).label
        (Y.atom j).label (Z.atom k).label).symm
  by_cases hBC : targetBC = sourceBC
  · subst targetBC
    by_cases hABC : targetABC = sourceABC
    · subst targetABC
      unfold rightSlotDelta
      rw [dif_pos rfl]
      rw [show hLabel = rfl by apply Subsingleton.elim]
      rw [AtomHom.coeff_id, Associator.rightDelta_source]
      exact (cast_algebra_one_of_label_eq shiftedReal.D hSource.symm _).symm
    · have hRoute :
          rightRouteSlot X Y Z i j k sourceBC sourceABC ≠
            rightRouteSlot X Y Z i j k sourceBC targetABC := by
        intro h
        have hpack :
            rightSlotPack shiftedReal.D shiftedReal.C X Y Z
                ⟨i, ⟨j, k, sourceBC⟩, sourceABC⟩ =
              rightSlotPack shiftedReal.D shiftedReal.C X Y Z
                ⟨i, ⟨j, k, sourceBC⟩, targetABC⟩ := by
          rw [rightSlotPack_route, rightSlotPack_route]
          exact h
        have hcoord :=
          (rightSlotPack shiftedReal.D shiftedReal.C X Y Z).injective hpack
        have : sourceABC = targetABC := by
          simp only [Sigma.mk.inj_iff, heq_iff_eq, true_and] at hcoord
          change sourceABC = targetABC at hcoord
          exact hcoord
        exact hABC this.symm
      unfold rightSlotDelta
      rw [dif_neg hRoute, AtomHom.coeff_zero]
      rw [Associator.rightDelta_off_second shiftedReal
        (X.atom i).label (Y.atom j).label (Z.atom k).label
        sourceBC sourceABC targetABC hABC]
      exact (cast_algebra_zero_of_label_eq shiftedReal.D hSource.symm _).symm
  · have hRoute :
        rightRouteSlot X Y Z i j k sourceBC sourceABC ≠
          rightRouteSlot X Y Z i j k targetBC targetABC := by
      intro h
      have hinner := congrArg
        (fun q => (Tensor.slots shiftedReal.D shiftedReal.C Y Z).get q.right) h
      have : sourceBC = targetBC := by
        simpa only [rightRouteSlot_inner, Sigma.mk.inj_iff,
          heq_iff_eq, true_and] using hinner
      exact hBC this.symm
    unfold rightSlotDelta
    rw [dif_neg hRoute, AtomHom.coeff_zero]
    rw [Associator.rightDelta_off_first shiftedReal
      (X.atom i).label (Y.atom j).label (Z.atom k).label
      sourceBC targetBC sourceABC targetABC hBC]
    exact (cast_algebra_zero_of_label_eq shiftedReal.D hSource.symm _).symm

private theorem realInvHom_route_sum_zero_of_left_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceBC : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (targetBC : shiftedReal.C.Index (Y.atom j').label (Z.atom k').label)
    (targetABC : shiftedReal.C.Index (X.atom i').label
      ((Y.atom j').label + (Z.atom k').label))
    (hi : i' ≠ i)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i' j' k' targetBC targetABC)).label) :
    ∑ qL : Tensor.Slot shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z,
      (AtomHom.comp
        (Associator.invEntry shiftedReal X Y Z
          (rightRouteSlot X Y Z i j k sourceBC sourceABC) qL)
        (Associator.homEntry shiftedReal X Y Z qL
          (rightRouteSlot X Y Z i' j' k' targetBC targetABC))).coeff hLabel = 0 := by
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  apply Finset.sum_eq_zero
  intro qL _
  by_cases hcompat :
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left).left =
        (rightRouteSlot X Y Z i j k sourceBC sourceABC).left
  · have htarget :
        ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left).left ≠
          (rightRouteSlot X Y Z i' j' k' targetBC targetABC).left := by
      intro h
      have hs := rightRouteSlot_left X Y Z i j k sourceBC sourceABC
      have ht := rightRouteSlot_left X Y Z i' j' k' targetBC targetABC
      exact hi (ht.symm.trans (h.symm.trans (hcompat.trans hs)))
    rw [realHomEntry_zero_of_left_ne X Y Z qL _ htarget]
    rw [AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _
  · rw [realInvEntry_zero_of_left_ne X Y Z _ qL hcompat]
    rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _

private theorem realInvHom_route_sum_zero_of_middle_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceBC : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (targetBC : shiftedReal.C.Index (Y.atom j').label (Z.atom k').label)
    (targetABC : shiftedReal.C.Index (X.atom i').label
      ((Y.atom j').label + (Z.atom k').label))
    (hj : j' ≠ j)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i' j' k' targetBC targetABC)).label) :
    ∑ qL : Tensor.Slot shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z,
      (AtomHom.comp
        (Associator.invEntry shiftedReal X Y Z
          (rightRouteSlot X Y Z i j k sourceBC sourceABC) qL)
        (Associator.homEntry shiftedReal X Y Z qL
          (rightRouteSlot X Y Z i' j' k' targetBC targetABC))).coeff hLabel = 0 := by
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  apply Finset.sum_eq_zero
  intro qL _
  by_cases hcompat :
      ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left).right =
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          (rightRouteSlot X Y Z i j k sourceBC sourceABC).right).left
  · have htarget :
        ((Tensor.slots shiftedReal.D shiftedReal.C X Y).get qL.left).right ≠
          ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
            (rightRouteSlot X Y Z i' j' k' targetBC targetABC).right).left := by
      intro h
      have hs := congrArg Sigma.fst
        (rightRouteSlot_inner X Y Z i j k sourceBC sourceABC)
      have ht := congrArg Sigma.fst
        (rightRouteSlot_inner X Y Z i' j' k' targetBC targetABC)
      exact hj (ht.symm.trans (h.symm.trans (hcompat.trans hs)))
    rw [realHomEntry_zero_of_middle_ne X Y Z qL _ htarget]
    rw [AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _
  · rw [realInvEntry_zero_of_middle_ne X Y Z _ qL hcompat]
    rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _

private theorem realInvHom_route_sum_zero_of_right_ne (X Y Z : Obj)
    (i : Fin X.size) (j : Fin Y.size) (k : Fin Z.size)
    (i' : Fin X.size) (j' : Fin Y.size) (k' : Fin Z.size)
    (sourceBC : shiftedReal.C.Index (Y.atom j).label (Z.atom k).label)
    (sourceABC : shiftedReal.C.Index (X.atom i).label
      ((Y.atom j).label + (Z.atom k).label))
    (targetBC : shiftedReal.C.Index (Y.atom j').label (Z.atom k').label)
    (targetABC : shiftedReal.C.Index (X.atom i').label
      ((Y.atom j').label + (Z.atom k').label))
    (hk : k' ≠ k)
    [Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label))]
    (hLabel :
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label =
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i' j' k' targetBC targetABC)).label) :
    ∑ qL : Tensor.Slot shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z,
      (AtomHom.comp
        (Associator.invEntry shiftedReal X Y Z
          (rightRouteSlot X Y Z i j k sourceBC sourceABC) qL)
        (Associator.homEntry shiftedReal X Y Z qL
          (rightRouteSlot X Y Z i' j' k' targetBC targetABC))).coeff hLabel = 0 := by
  classical
  letI : Fact (DLaws shiftedReal.D) :=
    ⟨realComputableShiftedRawDCT.laws.D⟩
  apply Finset.sum_eq_zero
  intro qL _
  by_cases hcompat : qL.right =
      ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
        (rightRouteSlot X Y Z i j k sourceBC sourceABC).right).right
  · have htarget : qL.right ≠
        ((Tensor.slots shiftedReal.D shiftedReal.C Y Z).get
          (rightRouteSlot X Y Z i' j' k' targetBC targetABC).right).right := by
      intro h
      have hs := congrArg (fun q => q.right)
        (rightRouteSlot_inner X Y Z i j k sourceBC sourceABC)
      have ht := congrArg (fun q => q.right)
        (rightRouteSlot_inner X Y Z i' j' k' targetBC targetABC)
      exact hk (ht.symm.trans (h.symm.trans (hcompat.trans hs)))
    rw [realHomEntry_zero_of_right_ne X Y Z qL _ htarget]
    rw [AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _
  · rw [realInvEntry_zero_of_right_ne X Y Z _ qL hcompat]
    rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
    exact AtomHom.coeff_zero _

private theorem rawInvHom_slot_entry (X Y Z : Obj)
    (qS qT : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length
        (fun m => AtomHom.comp
          (Associator.invEntry shiftedReal X Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m))
          (Associator.homEntry shiftedReal X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m) qT)) =
      rightSlotDelta X Y Z qS qT := by
  classical
  rcases exists_eq_rightRouteSlot X Y Z qS with
    ⟨i, j, k, sourceBC, sourceABC, hqS⟩
  rcases exists_eq_rightRouteSlot X Y Z qT with
    ⟨i', j', k', targetBC, targetABC, hqT⟩
  subst qS
  subst qT
  apply AtomHom.ext
  intro hLabel
  letI : Fact (SuperAlgebraLaws (shiftedReal.D.algebra
      (Tensor.slotAtom shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)
        (rightRouteSlot X Y Z i j k sourceBC sourceABC)).label)) :=
    ⟨realComputableShiftedRawDCT.laws.D.algebra_laws _⟩
  rw [coeff_finSum realComputableShiftedRawDCT.laws.D hLabel]
  rw [rawFinSum_eq_sum]
  let F := fun qL : Tensor.Slot shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z =>
    (AtomHom.comp
      (Associator.invEntry shiftedReal X Y Z
        (rightRouteSlot X Y Z i j k sourceBC sourceABC) qL)
      (Associator.homEntry shiftedReal X Y Z qL
        (rightRouteSlot X Y Z i' j' k' targetBC targetABC))).coeff hLabel
  change (∑ m : Fin (Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length,
        F ((Tensor.slots shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m)) = _
  rw [show (∑ m : Fin (Tensor.slots shiftedReal.D shiftedReal.C
      (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length,
        F ((Tensor.slots shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m)) =
      ∑ qL, F qL by
    simpa only [slotsEquiv_apply] using
      (slotsEquiv shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).sum_comp F]
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      by_cases hk : k' = k
      · subst k'
        calc
          _ = cast
              (congrArg (fun t : ZMod 8 =>
                (shiftedReal.D.algebra t).carrier)
                ((rightRouteSlot_label X Y Z i j k
                  sourceBC sourceABC).trans
                  (_root_.add_assoc (X.atom i).label
                    (Y.atom j).label (Z.atom k).label).symm).symm)
              (Associator.rightDelta shiftedReal
                (X.atom i).label (Y.atom j).label (Z.atom k).label
                sourceBC sourceABC targetBC targetABC) :=
            realInvHom_route_sum X Y Z i j k sourceBC targetBC
              sourceABC targetABC
          _ = _ := (rightRoute_delta_coeff X Y Z i j k
            sourceBC targetBC sourceABC targetABC hLabel).symm
      · rw [realInvHom_route_sum_zero_of_right_ne X Y Z
          i j k i j k' sourceBC sourceABC targetBC targetABC hk hLabel]
        unfold rightSlotDelta
        rw [dif_neg (rightRouteSlot_ne_of_right_ne X Y Z
          i j k i j k' sourceBC sourceABC targetBC targetABC hk)]
        exact (AtomHom.coeff_zero hLabel).symm
    · rw [realInvHom_route_sum_zero_of_middle_ne X Y Z
        i j k i j' k' sourceBC sourceABC targetBC targetABC hj hLabel]
      unfold rightSlotDelta
      rw [dif_neg (rightRouteSlot_ne_of_middle_ne X Y Z
        i j k i j' k' sourceBC sourceABC targetBC targetABC hj)]
      exact (AtomHom.coeff_zero hLabel).symm
  · rw [realInvHom_route_sum_zero_of_left_ne X Y Z
      i j k i' j' k' sourceBC sourceABC targetBC targetABC hi hLabel]
    unfold rightSlotDelta
    rw [dif_neg (rightRouteSlot_ne_of_left_ne X Y Z
      i j k i' j' k' sourceBC sourceABC targetBC targetABC hi)]
    exact (AtomHom.coeff_zero hLabel).symm


private theorem correctedInvHom_slot_entry (X Y Z : Obj)
    (qS qT : Tensor.Slot shiftedReal.D shiftedReal.C X
      (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) :
    AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length
        (fun m => AtomHom.comp
          (RealAssociator.invEntry X Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m))
          (RealAssociator.homEntry X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m) qT)) =
      rightSlotDelta X Y Z qS qT := by
  calc
    _ = AtomHom.finSum
        (Tensor.slots shiftedReal.D shiftedReal.C
          (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length
        (fun m => AtomHom.comp
          (Associator.invEntry shiftedReal X Y Z qS
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m))
          (Associator.homEntry shiftedReal X Y Z
            ((Tensor.slots shiftedReal.D shiftedReal.C
              (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m) qT)) := by
      apply AtomHom.finSum_congr
      intro m
      exact correctedInvHom_term X Y Z qS qT _
    _ = _ := rawInvHom_slot_entry X Y Z qS qT

theorem realAssociator_inv_hom (X Y Z : Obj) :
    Hom.comp (RealAssociator.inv X Y Z) (RealAssociator.hom X Y Z) =
      Hom.id shiftedReal.D
        (Tensor.obj shiftedReal.D shiftedReal.C X
          (Tensor.obj shiftedReal.D shiftedReal.C Y Z)) := by
  apply Hom.ext
  intro i k
  let qS := (Tensor.slots shiftedReal.D shiftedReal.C X
    (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get i
  let qT := (Tensor.slots shiftedReal.D shiftedReal.C X
    (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).get k
  unfold Hom.comp RealAssociator.inv RealAssociator.hom
  change AtomHom.finSum
      (Tensor.slots shiftedReal.D shiftedReal.C
        (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).length
      (fun m => AtomHom.comp
        (RealAssociator.invEntry X Y Z qS
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m))
        (RealAssociator.homEntry X Y Z
          ((Tensor.slots shiftedReal.D shiftedReal.C
            (Tensor.obj shiftedReal.D shiftedReal.C X Y) Z).get m) qT)) = _
  rw [correctedInvHom_slot_entry X Y Z qS qT]
  by_cases hik : i = k
  · subst k
    simp only [qS, qT, rightSlotDelta, dif_pos, Hom.id]
    rfl
  · have hq : qS ≠ qT := by
      intro h
      apply hik
      exact (slotsEquiv shiftedReal.D shiftedReal.C X
        (Tensor.obj shiftedReal.D shiftedReal.C Y Z)).injective
        (by simpa only [slotsEquiv_apply, qS, qT] using h)
    rw [rightSlotDelta, dif_neg hq]
    simp only [Hom.id, dif_neg hik]
    rfl

end RealAssociatorLaws

end Superfusion.RMod.FromRawDCT
