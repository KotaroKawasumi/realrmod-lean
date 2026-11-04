import Superfusion.RMod.FromRawDCT.RealCandidate
import Superfusion.RMod.FromRawDCT.RealAssociatorCoherence
import Superfusion.RMod.FromRawDCT.RealMiddleUnitConnectorCertificate
import Superfusion.RMod.FromRawDCT.RealUnitFaceTable
import Superfusion.Gauge.RealFuseSpecPilot

/-!
# Unit-face laws for the computably shifted real raw DCT

This concrete law file proves the two regular-action identities needed by
the coordinate unitors.  The statements mention only the already shifted
`realComputableShiftedRawDCT` and its exact chosen unit rows.  The proofs use
the existing semantic realization of the frozen fusion coefficients; no
shift cochain or numerical table is applied again.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT
open RModCoordinate
open RModCoordinate.FusionTable

/-! ## Raw semantic unit-face identities -/

/-- On the left unit face, the unique raw fusion coefficient is the input
coefficient transported along `0 + a = a`. -/
private theorem rawFusionCoefficient_left_unit (a : ZMod 8) (y : Coeff a) :
    fusionCoefficient 0 a (realUnitRowsData.left a)
        (realUnitRowsData.left a) (Coeff.one 0) y =
      cast (congrArg Coeff (zero_add a).symm) y := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ a = (n : ZMod 8) :=
    ⟨a.val, ZMod.val_lt a, (ZMod.natCast_zmod_val a).symm⟩
  interval_cases n <;>
    change _ = y <;>
    apply (Coeff.semantic _).injective <;>
    rw [FusionTableLaws.semantic_fusionCoefficient_eq_matrix_sum] <;>
    simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply] <;>
    simp [realFuseMatrix_zero_left, Coeff.one, realRepDim] <;>
    apply Finset.sum_congr rfl <;>
    intro i _ <;>
    congr 1 <;>
    convert (Fintype.sum_ite_eq i y) using 1 <;>
    simp [Fin.ext_iff] <;>
    rfl

/-- On the right unit face, the unique raw fusion coefficient is the input
coefficient transported along `a + 0 = a`. -/
private theorem rawFusionCoefficient_right_unit (a : ZMod 8) (x : Coeff a) :
    fusionCoefficient a 0 (realUnitRowsData.right a)
        (realUnitRowsData.right a) x (Coeff.one 0) =
      cast (congrArg Coeff (add_zero a).symm) x := by
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ a = (n : ZMod 8) :=
    ⟨a.val, ZMod.val_lt a, (ZMod.natCast_zmod_val a).symm⟩
  interval_cases n <;>
    change _ = x <;>
    apply (Coeff.semantic _).injective <;>
    rw [FusionTableLaws.semantic_fusionCoefficient_eq_matrix_sum] <;>
    simp only [Coeff.semantic, Module.Basis.equivFun_symm_apply] <;>
    simp [realFuseMatrix_zero_right, Coeff.one, realRepDim] <;>
    apply Finset.sum_congr rfl <;>
    intro i _ <;>
    congr 1 <;>
    convert (Fintype.sum_ite_eq i x) using 1 <;>
    simp [Fin.ext_iff] <;>
    rfl

/-! ## Identities for the exact shifted kernel data -/

/-- Normalization of the already bundled computable shift on the left
unit face. -/
private theorem realComputableShiftNu_left_unit (a : ZMod 8) :
    shiftNu realComputableShiftData.cochains 0 a = 0 := by
  change realComputableNuBeta.data.nu
      (Multiplicative.ofAdd 0) (Multiplicative.ofAdd a) = 0
  exact (realComputableNuBeta.laws.nu_normalized
    (Multiplicative.ofAdd a)).1

/-- Normalization of the already bundled computable shift on the right
unit face. -/
private theorem realComputableShiftNu_right_unit (a : ZMod 8) :
    shiftNu realComputableShiftData.cochains a 0 = 0 := by
  change realComputableNuBeta.data.nu
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd 0) = 0
  exact (realComputableNuBeta.laws.nu_normalized
    (Multiplicative.ofAdd a)).2

/-- The parity twist in the concrete coefficient algebra is the identity
at exponent zero. -/
private theorem realRouteRowTwist_zeroParity (a : ZMod 8)
    (x : (realDData.algebra a).carrier) :
    routeRowTwist realDData a 0 x = x :=
  routeRowTwist_zeroParity (realDData.algebra a)
    (realDLaws.algebra_laws a) x

/-- The exact shifted left-unit row acts regularly on an arbitrary
coefficient. -/
theorem realComputableShifted_leftCoeff_left_unit (a : ZMod 8)
    (y : (realComputableShiftedRawDCT.data.D.algebra a).carrier) :
    realComputableShiftedRawDCT.data.C.leftCoeff 0 a
        (realUnitRowsData.left a) (realUnitRowsData.left a)
        (realComputableShiftedRawDCT.data.D.algebra 0).one y =
      cast
        (congrArg
          (fun t : ZMod 8 =>
            (realComputableShiftedRawDCT.data.D.algebra t).carrier)
          (zero_add a).symm)
        y := by
  change fusionCoefficient 0 a
      (realUnitRowsData.left a) (realUnitRowsData.left a)
      (routeRowTwist realDData 0
        (shiftNu realComputableShiftData.cochains 0 a) (Coeff.one 0))
      (routeRowTwist realDData a
        (shiftNu realComputableShiftData.cochains 0 a) y) = _
  rw [realComputableShiftNu_left_unit]
  rw [realRouteRowTwist_zeroParity, realRouteRowTwist_zeroParity]
  exact rawFusionCoefficient_left_unit a y

/-- The exact shifted right-unit row acts regularly on an arbitrary
coefficient. -/
theorem realComputableShifted_leftCoeff_right_unit (a : ZMod 8)
    (x : (realComputableShiftedRawDCT.data.D.algebra a).carrier) :
    realComputableShiftedRawDCT.data.C.leftCoeff a 0
        (realUnitRowsData.right a) (realUnitRowsData.right a) x
        (realComputableShiftedRawDCT.data.D.algebra 0).one =
      cast
        (congrArg
          (fun t : ZMod 8 =>
            (realComputableShiftedRawDCT.data.D.algebra t).carrier)
          (add_zero a).symm)
        x := by
  change fusionCoefficient a 0
      (realUnitRowsData.right a) (realUnitRowsData.right a)
      (routeRowTwist realDData a
        (shiftNu realComputableShiftData.cochains a 0) x)
      (routeRowTwist realDData 0
        (shiftNu realComputableShiftData.cochains a 0) (Coeff.one 0)) = _
  rw [realComputableShiftNu_right_unit]
  rw [realRouteRowTwist_zeroParity, realRouteRowTwist_zeroParity]
  exact rawFusionCoefficient_right_unit a x

/-! ## Proof-layer transports and finite singleton reductions -/

private abbrev x : RawDCTData := realComputableShiftedRawDCT.data

private theorem zmod2_add_self (i : ZMod 2) : i + i = 0 := by
  fin_cases i <;> rfl

private theorem cast_algebra_one (dD : DData) {a b : ZMod 8}
    (h : a = b) :
    cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h)
        (dD.algebra a).one = (dD.algebra b).one := by
  subst b
  rfl

private theorem cast_cast_eq {A B C : Type} (hAB : A = B) (hBC : B = C)
    (u : A) : cast hBC (cast hAB u) = cast (hAB.trans hBC) u := by
  subst B
  subst C
  rfl

private theorem cast_algebra_one_symm (dD : DData) {a b : ZMod 8}
    (h : a = b) :
    cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier) h).symm
        (dD.algebra b).one = (dD.algebra a).one := by
  subst b
  rfl

private theorem cast_algebra_one_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier) :
    cast h (dD.algebra a).one = (dD.algebra b).one := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
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

private theorem cast_algebra_add_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier)
    (u v : (dD.algebra a).carrier) :
    cast h ((dD.algebra a).add u v) =
      (dD.algebra b).add (cast h u) (cast h v) := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem cast_mul_eq_one_of_label_eq (dD : DData)
    {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier)
    (u v : (dD.algebra a).carrier)
    (huv : (dD.algebra a).mul u v = (dD.algebra a).one) :
    (dD.algebra b).mul (cast h u) (cast h v) =
      (dD.algebra b).one := by
  rw [← cast_algebra_mul_of_label_eq dD hab h, huv]
  exact cast_algebra_one_of_label_eq dD hab h

private theorem cast_algebra_memGrade_of_label_eq (dD : DData)
    (_hD : DLaws dD) {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier)
    (i : ZMod 2) (y : (dD.algebra a).carrier)
    (hy : (dD.algebra a).MemGrade i y) :
    (dD.algebra b).MemGrade i (cast h y) := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  exact hy

private theorem leftCoeff_transport_first_to_zero (x : RawDCTData)
    (a₀ a : ZMod 8) (h₀ : a₀ = 0)
    (target source : x.C.Index a₀ a)
    (u : (x.D.algebra a₀).carrier) (v : (x.D.algebra a).carrier) :
    x.C.leftCoeff a₀ a target source u v =
      cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
        (congrArg (fun t : ZMod 8 => t + a) h₀)).symm
        (x.C.leftCoeff 0 a
          (Associator.castIndex x h₀ rfl target)
          (Associator.castIndex x h₀ rfl source)
          (cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier) h₀) u)
          v) := by
  subst a₀
  congr

private theorem rawFinSum_eq_single_of_unique (d : SuperAlgebraData ℝ)
    (hd : SuperAlgebraLaws d) {n : ℕ} (k : Fin n)
    (hunique : ∀ i : Fin n, i = k) (f : Fin n → d.carrier) :
    CData.rawFinSum d f = f k := by
  have hnpos : 0 < n := Nat.zero_lt_of_lt k.isLt
  have hnle : n ≤ 1 := by
    by_contra hn
    have htwo : 2 ≤ n := by omega
    let i : Fin n := ⟨1, by omega⟩
    let z : Fin n := ⟨0, hnpos⟩
    have hzi : z = i := (hunique z).trans (hunique i).symm
    have hi := congrArg Fin.val hzi
    simp [z, i] at hi
  have hn : n = 1 := by omega
  subst n
  have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
  subst k
  have hf : f = fun _ => f 0 := by
    funext i
    exact congrArg f (Subsingleton.elim _ _)
  rw [hf]
  change d.add (f 0) d.zero = f 0
  exact hd.add_zero _

private theorem castIndex_injective (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b') :
    Function.Injective (Associator.castIndex x ha hb) := by
  subst a'
  subst b'
  intro r r' h
  exact h

private theorem castIndex_val (x : RawDCTData)
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    (Associator.castIndex x ha hb r).val = r.val := by
  subst a'
  subst b'
  rfl

private theorem realLeftUnitIndex_val_zero (a : ZMod 8)
    (r : x.C.Index 0 a) : r.val = 0 := by
  have h := congrArg Fin.val (realUnitRowsLaws.left_unique a r)
  simpa [realUnitRowsData] using h

/-! ## Unique coordinate slots on the two unit faces -/

private def leftUnitSlot (X : Obj) (j : Fin X.size) :
    Tensor.Slot x.D x.C Unitor.unit X :=
  ⟨⟨0, Nat.zero_lt_one⟩,
    ⟨j, realUnitRowsData.left (X.atom j).label⟩⟩

private theorem leftUnitSlot_mem (X : Obj) (j : Fin X.size) :
    leftUnitSlot X j ∈ Tensor.slots x.D x.C Unitor.unit X := by
  unfold leftUnitSlot Tensor.slots
  rw [List.mem_sigma]
  constructor
  · exact List.mem_ofFn.mpr ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
  · rw [List.mem_sigma]
    constructor
    · exact List.mem_ofFn.mpr ⟨j, rfl⟩
    · exact List.mem_ofFn.mpr
        ⟨realUnitRowsData.left (X.atom j).label, rfl⟩

private theorem leftUnitSlot_exists (X : Obj) (j : Fin X.size) :
    ∃ k : Fin (Tensor.obj x.D x.C Unitor.unit X).size,
      (Tensor.slots x.D x.C Unitor.unit X).get k = leftUnitSlot X j := by
  exact List.get_of_mem (leftUnitSlot_mem X j)

private theorem slots_get_injective {X Y : Obj}
    {i j : Fin (Tensor.obj x.D x.C X Y).size}
    (h : (Tensor.slots x.D x.C X Y).get i =
      (Tensor.slots x.D x.C X Y).get j) : i = j := by
  exact (Tensor.slots_nodup x.D x.C X Y).get_inj_iff.mp h

private theorem leftUnitSlot_eq (X : Obj)
    (q : Tensor.Slot x.D x.C Unitor.unit X) :
    q = leftUnitSlot X q.right := by
  rcases q with ⟨qi, qj, qr⟩
  have hi : qi = (⟨0, Nat.zero_lt_one⟩ : Fin Unitor.unit.size) := by
    apply Fin.ext
    have hqi : qi.val < 1 := by
      simpa [Unitor.unit, Obj.singleton, Obj.size] using qi.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hqi)
  subst qi
  have hr : qr = realUnitRowsData.left (X.atom qj).label :=
    realUnitRowsLaws.left_unique _ qr
  subst qr
  rfl

private theorem leftSlot_right_injective (X : Obj)
    (q q' : Tensor.Slot x.D x.C Unitor.unit X)
    (h : q.right = q'.right) : q = q' := by
  rw [leftUnitSlot_eq X q, leftUnitSlot_eq X q', h]

private theorem leftIndex_right_injective (X : Obj)
    (i j : Fin (Tensor.obj x.D x.C Unitor.unit X).size)
    (h : ((Tensor.slots x.D x.C Unitor.unit X).get i).right =
      ((Tensor.slots x.D x.C Unitor.unit X).get j).right) : i = j := by
  apply slots_get_injective
  exact leftSlot_right_injective X _ _ h

private theorem leftSlotAtom_eq (X : Obj)
    (q : Tensor.Slot x.D x.C Unitor.unit X) :
    Tensor.slotAtom x.D x.C Unitor.unit X q = X.atom q.right := by
  apply Prod.ext
  · change 0 + (X.atom q.right).label = (X.atom q.right).label
    exact zero_add _
  · change 0 + (X.atom q.right).shift +
        x.C.rowParity 0 (X.atom q.right).label q.fusion =
      (X.atom q.right).shift
    rw [realUnitRowsLaws.left_unique _ q.fusion,
      realUnitRowsLaws.left_even]
    simp

private def rightUnitSlot (X : Obj) (i : Fin X.size) :
    Tensor.Slot x.D x.C X Unitor.unit :=
  ⟨i, ⟨⟨0, Nat.zero_lt_one⟩,
    realUnitRowsData.right (X.atom i).label⟩⟩

private theorem rightUnitSlot_mem (X : Obj) (i : Fin X.size) :
    rightUnitSlot X i ∈ Tensor.slots x.D x.C X Unitor.unit := by
  unfold rightUnitSlot Tensor.slots
  rw [List.mem_sigma]
  constructor
  · exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · rw [List.mem_sigma]
    constructor
    · exact List.mem_ofFn.mpr ⟨⟨0, Nat.zero_lt_one⟩, rfl⟩
    · exact List.mem_ofFn.mpr
        ⟨realUnitRowsData.right (X.atom i).label, rfl⟩

private theorem rightUnitSlot_eq (X : Obj)
    (q : Tensor.Slot x.D x.C X Unitor.unit) :
    q = rightUnitSlot X q.left := by
  rcases q with ⟨qi, qj, qr⟩
  have hj : qj = (⟨0, Nat.zero_lt_one⟩ : Fin Unitor.unit.size) := by
    apply Fin.ext
    have hqj : qj.val < 1 := by
      simpa [Unitor.unit, Obj.singleton, Obj.size] using qj.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hqj)
  subst qj
  have hr : qr = realUnitRowsData.right (X.atom qi).label :=
    realUnitRowsLaws.right_unique _ qr
  subst qr
  rfl

private theorem rightSlot_left_injective (X : Obj)
    (q q' : Tensor.Slot x.D x.C X Unitor.unit)
    (h : q.left = q'.left) : q = q' := by
  rw [rightUnitSlot_eq X q, rightUnitSlot_eq X q', h]

private theorem rightUnitSlot_exists (X : Obj) (i : Fin X.size) :
    ∃ k : Fin (Tensor.obj x.D x.C X Unitor.unit).size,
      (Tensor.slots x.D x.C X Unitor.unit).get k = rightUnitSlot X i := by
  exact List.get_of_mem (rightUnitSlot_mem X i)

private theorem rightIndex_left_injective (X : Obj)
    (i j : Fin (Tensor.obj x.D x.C X Unitor.unit).size)
    (h : ((Tensor.slots x.D x.C X Unitor.unit).get i).left =
      ((Tensor.slots x.D x.C X Unitor.unit).get j).left) : i = j := by
  apply slots_get_injective
  exact rightSlot_left_injective X _ _ h

private theorem rightSlotAtom_eq (X : Obj)
    (q : Tensor.Slot x.D x.C X Unitor.unit) :
    Tensor.slotAtom x.D x.C X Unitor.unit q = X.atom q.left := by
  apply Prod.ext
  · change (X.atom q.left).label + 0 = (X.atom q.left).label
    exact add_zero _
  · change (X.atom q.left).shift + 0 +
        x.C.rowParity (X.atom q.left).label 0 q.fusion =
      (X.atom q.left).shift
    rw [realUnitRowsLaws.right_unique _ q.fusion,
      realUnitRowsLaws.right_even]
    simp

/-! ## Two-sided inverse laws for the right unitor -/

private theorem rightEntry_comp_self (X : Obj)
    (q : Tensor.Slot x.D x.C X Unitor.unit) :
    AtomHom.comp (Unitor.rightHomEntry x X q q.left)
        (Unitor.rightInvEntry x X q.left q) =
      AtomHom.id x.D (Tensor.slotAtom x.D x.C X Unitor.unit q) := by
  apply AtomHom.ext
  intro hLabel
  have h₁ : (Tensor.slotAtom x.D x.C X Unitor.unit q).label =
      (X.atom q.left).label := by
    change (X.atom q.left).label + 0 = (X.atom q.left).label
    exact add_zero _
  have h₂ : (X.atom q.left).label =
      (Tensor.slotAtom x.D x.C X Unitor.unit q).label := h₁.symm
  have hh : hLabel = h₁.trans h₂ := Subsingleton.elim _ _
  cases hh
  rw [AtomHom.coeff_comp _ _ h₁ h₂]
  simp [Unitor.rightHomEntry, Unitor.rightInvEntry]
  simpa only [cast_algebra_one_of_label_eq x.D h₂,
    cast_algebra_one_of_label_eq x.D h₁] using
    (realComputableShiftedRawDCT.laws.D.algebra_laws
      (Tensor.slotAtom x.D x.C X Unitor.unit q).label).one_mul
      (x.D.algebra
        (Tensor.slotAtom x.D x.C X Unitor.unit q).label).one

private theorem rightEntry_reverse_comp_self (X : Obj)
    (q : Tensor.Slot x.D x.C X Unitor.unit) :
    AtomHom.comp (Unitor.rightInvEntry x X q.left q)
        (Unitor.rightHomEntry x X q q.left) =
      AtomHom.id x.D (X.atom q.left) := by
  apply AtomHom.ext
  intro hLabel
  have h₁ : (X.atom q.left).label =
      (Tensor.slotAtom x.D x.C X Unitor.unit q).label := by
    change (X.atom q.left).label = (X.atom q.left).label + 0
    exact (add_zero _).symm
  have h₂ : (Tensor.slotAtom x.D x.C X Unitor.unit q).label =
      (X.atom q.left).label := h₁.symm
  have hh : hLabel = h₁.trans h₂ := Subsingleton.elim _ _
  cases hh
  rw [AtomHom.coeff_comp _ _ h₁ h₂]
  simp [Unitor.rightHomEntry, Unitor.rightInvEntry]
  simpa only [cast_algebra_one_of_label_eq x.D h₂,
    cast_algebra_one_of_label_eq x.D h₁] using
    (realComputableShiftedRawDCT.laws.D.algebra_laws
      (X.atom q.left).label).one_mul
      (x.D.algebra (X.atom q.left).label).one

/-- The canonical real right unitor followed by its stored inverse is the
identity on `X ⊗ 𝟙`. -/
theorem realRightUnitor_hom_inv (X : Obj) :
    Hom.comp (Unitor.rightHom x X) (Unitor.rightInv x X) =
      Hom.id x.D (Tensor.obj x.D x.C X Unitor.unit) := by
  apply Hom.ext
  intro i k
  let q := (Tensor.slots x.D x.C X Unitor.unit).get i
  let q' := (Tensor.slots x.D x.C X Unitor.unit).get k
  by_cases hik : i = k
  · subst k
    unfold Hom.comp Unitor.rightHom Unitor.rightInv
    rw [show Hom.id x.D (Tensor.obj x.D x.C X Unitor.unit) i i =
        AtomHom.id x.D ((Tensor.obj x.D x.C X Unitor.unit).atom i) by
      simp [Hom.id]]
    change AtomHom.finSum X.size (fun j =>
        AtomHom.comp (Unitor.rightHomEntry x X
            ((Tensor.slots x.D x.C X Unitor.unit).get i) j)
          (Unitor.rightInvEntry x X j
            ((Tensor.slots x.D x.C X Unitor.unit).get i))) =
      AtomHom.id x.D (Tensor.slotAtom x.D x.C X Unitor.unit
        ((Tensor.slots x.D x.C X Unitor.unit).get i))
    let q := (Tensor.slots x.D x.C X Unitor.unit).get i
    calc
      _ = AtomHom.finSum X.size (fun j =>
          if j = q.left then
            AtomHom.id x.D (Tensor.slotAtom x.D x.C X Unitor.unit q)
          else AtomHom.zero x.D _ _) := by
        apply AtomHom.finSum_congr
        intro j
        by_cases hj : j = q.left
        · subst j
          simpa only [q, if_pos] using rightEntry_comp_self X q
        · have hz : Unitor.rightHomEntry x X q j =
              AtomHom.zero x.D _ _ := by
            simp [Unitor.rightHomEntry, Ne.symm hj]
          rw [hz, AtomHom.zero_comp
            realComputableShiftedRawDCT.laws.D]
          simpa only [q, hj, if_false]
      _ = _ := AtomHom.finSum_single
        realComputableShiftedRawDCT.laws.D q.left _
  · have hqq' : q.left ≠ q'.left := by
      intro h
      exact hik (rightIndex_left_injective X i k h)
    dsimp [q, q'] at hqq' ⊢
    unfold Hom.comp Unitor.rightHom Unitor.rightInv
    rw [show Hom.id x.D (Tensor.obj x.D x.C X Unitor.unit) i k =
        AtomHom.zero x.D _ _ by simp [Hom.id, hik]]
    change AtomHom.finSum X.size (fun j =>
        AtomHom.comp (Unitor.rightHomEntry x X q j)
          (Unitor.rightInvEntry x X j q')) =
      AtomHom.zero x.D _ _
    rw [AtomHom.finSum_congr (g := fun _ => AtomHom.zero x.D _ _)]
    · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
    · intro j
      by_cases hj : j = q.left
      · have hj' : j ≠ q'.left := by
          intro h'
          exact hqq' (hj.symm.trans h')
        have hz : Unitor.rightInvEntry x X j q' =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.rightInvEntry, hj']
        rw [hz, AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
      · have hz : Unitor.rightHomEntry x X q j =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.rightHomEntry, Ne.symm hj]
        rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]

/-- The stored inverse right unitor followed by the forward map is the
identity on `X`. -/
theorem realRightUnitor_inv_hom (X : Obj) :
    Hom.comp (Unitor.rightInv x X) (Unitor.rightHom x X) =
      Hom.id x.D X := by
  apply Hom.ext
  intro i k
  by_cases hik : i = k
  · subst k
    obtain ⟨p, hp⟩ := rightUnitSlot_exists X i
    let q := (Tensor.slots x.D x.C X Unitor.unit).get p
    have hqleft : q.left = i := by
      change ((Tensor.slots x.D x.C X Unitor.unit).get p).left = i
      exact (congrArg Tensor.Slot.left hp).trans rfl
    unfold Hom.comp Unitor.rightInv Unitor.rightHom
    rw [show Hom.id x.D X i i = AtomHom.id x.D (X.atom i) by
      simp [Hom.id]]
    change AtomHom.finSum (Tensor.obj x.D x.C X Unitor.unit).size
        (fun j => AtomHom.comp
          (Unitor.rightInvEntry x X i
            ((Tensor.slots x.D x.C X Unitor.unit).get j))
          (Unitor.rightHomEntry x X
            ((Tensor.slots x.D x.C X Unitor.unit).get j) i)) =
      AtomHom.id x.D (X.atom i)
    calc
      _ = AtomHom.finSum (Tensor.obj x.D x.C X Unitor.unit).size
          (fun j => if j = p then AtomHom.id x.D (X.atom i)
            else AtomHom.zero x.D _ _) := by
        apply AtomHom.finSum_congr
        intro j
        by_cases hj : j = p
        · subst j
          simp only [if_pos]
          change AtomHom.comp (Unitor.rightInvEntry x X i q)
              (Unitor.rightHomEntry x X q i) =
            AtomHom.id x.D (X.atom i)
          rw [← hqleft]
          exact rightEntry_reverse_comp_self X q
        · have hleft :
            ((Tensor.slots x.D x.C X Unitor.unit).get j).left ≠ i := by
            intro h
            have hjp := rightIndex_left_injective X j p (h.trans hqleft.symm)
            exact hj hjp
          have hz : Unitor.rightInvEntry x X i
              ((Tensor.slots x.D x.C X Unitor.unit).get j) =
              AtomHom.zero x.D _ _ := by
            unfold Unitor.rightInvEntry
            simp only [dif_neg (Ne.symm hleft)]
          rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
          simp only [hj, if_false]
      _ = _ := AtomHom.finSum_single
        realComputableShiftedRawDCT.laws.D p _
  · unfold Hom.comp Unitor.rightInv Unitor.rightHom
    rw [show Hom.id x.D X i k = AtomHom.zero x.D _ _ by
      simp [Hom.id, hik]]
    change AtomHom.finSum (Tensor.obj x.D x.C X Unitor.unit).size
        (fun j => AtomHom.comp
          (Unitor.rightInvEntry x X i
            ((Tensor.slots x.D x.C X Unitor.unit).get j))
          (Unitor.rightHomEntry x X
            ((Tensor.slots x.D x.C X Unitor.unit).get j) k)) =
      AtomHom.zero x.D _ _
    rw [AtomHom.finSum_congr (g := fun _ => AtomHom.zero x.D _ _)]
    · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
    · intro j
      let q := (Tensor.slots x.D x.C X Unitor.unit).get j
      by_cases hi : i = q.left
      · have hk : q.left ≠ k := by
          intro h
          exact hik (hi.trans h)
        have hz : Unitor.rightHomEntry x X q k =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.rightHomEntry, hk]
        rw [hz, AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
      · have hz : Unitor.rightInvEntry x X i q =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.rightInvEntry, hi]
        rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]

/-! ## Evenness of the right unitor -/

private theorem rightHomEntry_even (X : Obj)
    (q : Tensor.Slot x.D x.C X Unitor.unit) (j : Fin X.size) :
    AtomHom.MemGrade 0 (Unitor.rightHomEntry x X q j) := by
  by_cases hj : q.left = j
  · subst j
    intro hLabel
    have hrow : x.C.rowParity (X.atom q.left).label 0 q.fusion = 0 := by
      rw [realUnitRowsLaws.right_unique _ q.fusion]
      exact realUnitRowsLaws.right_even _
    have hdegree : 0 +
        (Tensor.slotAtom x.D x.C X Unitor.unit q).shift +
        (X.atom q.left).shift = 0 := by
      change 0 + ((X.atom q.left).shift + 0 +
          x.C.rowParity (X.atom q.left).label 0 q.fusion) +
        (X.atom q.left).shift = 0
      rw [hrow]
      simpa only [add_zero, zero_add] using
        zmod2_add_self (X.atom q.left).shift
    rw [hdegree]
    simp [Unitor.rightHomEntry]
    apply cast_algebra_memGrade_of_label_eq x.D
      realComputableShiftedRawDCT.laws.D
      (a := (X.atom q.left).label)
      (b := (Tensor.slotAtom x.D x.C X Unitor.unit q).label)
      (add_zero _).symm
    exact (realComputableShiftedRawDCT.laws.D.algebra_laws _).one_mem
  · rw [show Unitor.rightHomEntry x X q j = AtomHom.zero x.D _ _ by
      unfold Unitor.rightHomEntry
      simp only [dif_neg hj]]
    exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0

private theorem rightInvEntry_even (X : Obj) (i : Fin X.size)
    (q : Tensor.Slot x.D x.C X Unitor.unit) :
    AtomHom.MemGrade 0 (Unitor.rightInvEntry x X i q) := by
  by_cases hi : i = q.left
  · subst i
    intro hLabel
    have hrow : x.C.rowParity (X.atom q.left).label 0 q.fusion = 0 := by
      rw [realUnitRowsLaws.right_unique _ q.fusion]
      exact realUnitRowsLaws.right_even _
    have hdegree : 0 + (X.atom q.left).shift +
        (Tensor.slotAtom x.D x.C X Unitor.unit q).shift = 0 := by
      change 0 + (X.atom q.left).shift +
        ((X.atom q.left).shift + 0 +
          x.C.rowParity (X.atom q.left).label 0 q.fusion) = 0
      rw [hrow]
      simpa only [add_zero, zero_add] using
        zmod2_add_self (X.atom q.left).shift
    rw [hdegree]
    simp [Unitor.rightInvEntry]
    exact (realComputableShiftedRawDCT.laws.D.algebra_laws _).one_mem
  · rw [show Unitor.rightInvEntry x X i q = AtomHom.zero x.D _ _ by
      unfold Unitor.rightInvEntry
      simp only [dif_neg hi]]
    exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0

/-- The forward real right unitor is even. -/
theorem realRightUnitor_hom_even (X : Obj) :
    Hom.MemGrade 0 (Unitor.rightHom x X) := by
  intro i j
  exact rightHomEntry_even X
    ((Tensor.slots x.D x.C X Unitor.unit).get i) j

/-- The inverse real right unitor is even. -/
theorem realRightUnitor_inv_even (X : Obj) :
    Hom.MemGrade 0 (Unitor.rightInv x X) := by
  intro i j
  exact rightInvEntry_even X i
    ((Tensor.slots x.D x.C X Unitor.unit).get j)

/-! ## Two-sided inverse laws for the left unitor -/

private theorem leftRaw_hom_inv_product (a : ZMod 8)
    (r : x.C.Index 0 a) :
    (x.D.algebra (0 + 0 + a)).mul
        (Associator.homCoefficient x 0 0 a
          (realUnitRowsData.left 0)
          (Associator.castIndex x (zero_add 0).symm rfl r)
          r (Associator.castIndex x rfl (zero_add a).symm r))
        (Associator.invCoefficient x 0 0 a
          r (Associator.castIndex x rfl (zero_add a).symm r)
          (realUnitRowsData.left 0)
          (Associator.castIndex x (zero_add 0).symm rfl r)) =
      (x.D.algebra (0 + 0 + a)).one := by
  let rightABC := Associator.castIndex x
    (a := 0) (b := a) (a' := 0) (b' := 0 + a)
    rfl (zero_add a).symm r
  let leftABC := Associator.castIndex x
    (a := 0) (b := a) (a' := 0 + 0) (b' := a)
    (zero_add 0).symm rfl r
  have h := Associator.hom_invCoefficient_matrix_identity x
    realComputableShiftedRawDCT.laws 0 0 a
    r rightABC r rightABC
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _)
      (realUnitRowsData.left 0)
      (realUnitRowsLaws.left_unique 0)] at h
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _)
      leftABC (fun i => by
        apply castIndex_injective x (zero_add 0) rfl
        exact (realUnitRowsLaws.left_unique a
            (Associator.castIndex x (zero_add 0) rfl i)).trans
          (realUnitRowsLaws.left_unique a
            (Associator.castIndex x (zero_add 0) rfl leftABC)).symm)] at h
  have hright : rightABC = r := by
    apply Fin.ext
    exact (realLeftUnitIndex_val_zero a rightABC).trans
      (realLeftUnitIndex_val_zero a r).symm
  rw [hright] at h
  have h' :
      (x.D.algebra (0 + 0 + a)).mul
          (Associator.homCoefficient x 0 0 a
            (realUnitRowsData.left 0) leftABC r r)
          (Associator.invCoefficient x 0 0 a r r
            (realUnitRowsData.left 0) leftABC) =
        (x.D.algebra (0 + 0 + a)).one := by
    simpa only [Associator.rightDelta_source] using h
  simpa only [rightABC, leftABC, hright] using h'

private theorem leftRaw_inv_hom_product (a : ZMod 8)
    (r : x.C.Index 0 a) :
    (x.D.algebra (0 + 0 + a)).mul
        (Associator.invCoefficient x 0 0 a
          r (Associator.castIndex x rfl (zero_add a).symm r)
          (realUnitRowsData.left 0)
          (Associator.castIndex x (zero_add 0).symm rfl r))
        (Associator.homCoefficient x 0 0 a
          (realUnitRowsData.left 0)
          (Associator.castIndex x (zero_add 0).symm rfl r)
          r (Associator.castIndex x rfl (zero_add a).symm r)) =
      (x.D.algebra (0 + 0 + a)).one := by
  let leftABC := Associator.castIndex x
    (a := 0) (b := a) (a' := 0 + 0) (b' := a)
    (zero_add 0).symm rfl r
  let rightABC := Associator.castIndex x
    (a := 0) (b := a) (a' := 0) (b' := 0 + a)
    rfl (zero_add a).symm r
  have h := Associator.inv_homCoefficient_matrix_identity x
    realComputableShiftedRawDCT.laws 0 0 a
    (realUnitRowsData.left 0)
    leftABC
    (realUnitRowsData.left 0)
    leftABC
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _)
      r (fun i => (realUnitRowsLaws.left_unique a i).trans
        (realUnitRowsLaws.left_unique a r).symm)] at h
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _)
      rightABC (fun i => by
        apply castIndex_injective x rfl (zero_add a)
        exact (realUnitRowsLaws.left_unique a
            (Associator.castIndex x rfl (zero_add a) i)).trans
          (realUnitRowsLaws.left_unique a
            (Associator.castIndex x rfl (zero_add a) rightABC)).symm)] at h
  have hright : rightABC = r := by
    apply Fin.ext
    exact (realLeftUnitIndex_val_zero a rightABC).trans
      (realLeftUnitIndex_val_zero a r).symm
  rw [hright] at h
  have hleftVal : leftABC.val = 0 := by
    have hv := realLeftUnitIndex_val_zero a
      (Associator.castIndex x (zero_add 0) rfl leftABC)
    simpa only [castIndex_val] using hv
  have hleft : leftABC = realUnitRowsData.left 0 := by
    apply Fin.ext
    simpa [realUnitRowsData] using hleftVal
  rw [hleft] at h
  have h' :
      (x.D.algebra (0 + 0 + a)).mul
          (Associator.invCoefficient x 0 0 a r r
            (realUnitRowsData.left 0) (realUnitRowsData.left 0))
          (Associator.homCoefficient x 0 0 a
            (realUnitRowsData.left 0) (realUnitRowsData.left 0) r r) =
        (x.D.algebra (0 + 0 + a)).one := by
    simpa only [Associator.leftDelta_source] using h
  simpa only [rightABC, leftABC, hright, hleft] using h'

private theorem leftCoefficient_hom_inv (a : ZMod 8)
    (r : x.C.Index 0 a) :
    (x.D.algebra a).mul
        (Unitor.leftInvCoefficient x realUnitRowsData a r)
        (Unitor.leftHomCoefficient x realUnitRowsData a r) =
      (x.D.algebra a).one := by
  have h := congrArg (Unitor.castUnitTriple x a)
    (leftRaw_hom_inv_product a r)
  have hlabel : 0 + 0 + a = a := by
    simp only [zero_add]
  unfold Unitor.leftInvCoefficient Unitor.leftHomCoefficient
  unfold Unitor.castUnitTriple at h ⊢
  simpa only [cast_algebra_mul_of_label_eq x.D hlabel,
    cast_algebra_one_of_label_eq x.D hlabel] using h

private theorem leftCoefficient_inv_hom (a : ZMod 8)
    (r : x.C.Index 0 a) :
    (x.D.algebra a).mul
        (Unitor.leftHomCoefficient x realUnitRowsData a r)
        (Unitor.leftInvCoefficient x realUnitRowsData a r) =
      (x.D.algebra a).one := by
  have h := congrArg (Unitor.castUnitTriple x a)
    (leftRaw_inv_hom_product a r)
  have hlabel : 0 + 0 + a = a := by
    simp only [zero_add]
  unfold Unitor.leftInvCoefficient Unitor.leftHomCoefficient
  unfold Unitor.castUnitTriple at h ⊢
  simpa only [cast_algebra_mul_of_label_eq x.D hlabel,
    cast_algebra_one_of_label_eq x.D hlabel] using h

private theorem leftEntry_comp_self (X : Obj)
    (q : Tensor.Slot x.D x.C Unitor.unit X) :
    AtomHom.comp (Unitor.leftHomEntry x realUnitRowsData X q q.right)
        (Unitor.leftInvEntry x realUnitRowsData X q.right q) =
      AtomHom.id x.D (Tensor.slotAtom x.D x.C Unitor.unit X q) := by
  apply AtomHom.ext
  intro hLabel
  have h₁ : (Tensor.slotAtom x.D x.C Unitor.unit X q).label =
      (X.atom q.right).label := by
    change 0 + (X.atom q.right).label = (X.atom q.right).label
    exact zero_add _
  have h₂ : (X.atom q.right).label =
      (Tensor.slotAtom x.D x.C Unitor.unit X q).label := h₁.symm
  have hh : hLabel = h₁.trans h₂ := Subsingleton.elim _ _
  cases hh
  rw [AtomHom.coeff_comp _ _ h₁ h₂]
  simp [Unitor.leftHomEntry, Unitor.leftInvEntry]
  apply cast_mul_eq_one_of_label_eq x.D h₂
  exact leftCoefficient_hom_inv (X.atom q.right).label q.fusion

private theorem leftEntry_reverse_comp_self (X : Obj)
    (q : Tensor.Slot x.D x.C Unitor.unit X) :
    AtomHom.comp (Unitor.leftInvEntry x realUnitRowsData X q.right q)
        (Unitor.leftHomEntry x realUnitRowsData X q q.right) =
      AtomHom.id x.D (X.atom q.right) := by
  apply AtomHom.ext
  intro hLabel
  have h₁ : (X.atom q.right).label =
      (Tensor.slotAtom x.D x.C Unitor.unit X q).label := by
    change (X.atom q.right).label = 0 + (X.atom q.right).label
    exact (zero_add _).symm
  have h₂ : (Tensor.slotAtom x.D x.C Unitor.unit X q).label =
      (X.atom q.right).label := h₁.symm
  have hh : hLabel = h₁.trans h₂ := Subsingleton.elim _ _
  cases hh
  rw [AtomHom.coeff_comp _ _ h₁ h₂]
  simp [Unitor.leftHomEntry, Unitor.leftInvEntry]
  exact leftCoefficient_inv_hom (X.atom q.right).label q.fusion

/-- The canonical real left unitor followed by its stored inverse is the
identity on `𝟙 ⊗ X`. -/
theorem realLeftUnitor_hom_inv (X : Obj) :
    Hom.comp (Unitor.leftHom x realUnitRowsData X)
        (Unitor.leftInv x realUnitRowsData X) =
      Hom.id x.D (Tensor.obj x.D x.C Unitor.unit X) := by
  apply Hom.ext
  intro i k
  let q := (Tensor.slots x.D x.C Unitor.unit X).get i
  let q' := (Tensor.slots x.D x.C Unitor.unit X).get k
  by_cases hik : i = k
  · subst k
    unfold Hom.comp Unitor.leftHom Unitor.leftInv
    rw [show Hom.id x.D (Tensor.obj x.D x.C Unitor.unit X) i i =
        AtomHom.id x.D ((Tensor.obj x.D x.C Unitor.unit X).atom i) by
      simp [Hom.id]]
    change AtomHom.finSum X.size (fun j =>
        AtomHom.comp (Unitor.leftHomEntry x realUnitRowsData X
            ((Tensor.slots x.D x.C Unitor.unit X).get i) j)
          (Unitor.leftInvEntry x realUnitRowsData X j
            ((Tensor.slots x.D x.C Unitor.unit X).get i))) =
      AtomHom.id x.D (Tensor.slotAtom x.D x.C Unitor.unit X
        ((Tensor.slots x.D x.C Unitor.unit X).get i))
    let q := (Tensor.slots x.D x.C Unitor.unit X).get i
    calc
      _ = AtomHom.finSum X.size (fun j =>
          if j = q.right then
            AtomHom.id x.D (Tensor.slotAtom x.D x.C Unitor.unit X q)
          else AtomHom.zero x.D _ _) := by
        apply AtomHom.finSum_congr
        intro j
        by_cases hj : j = q.right
        · subst j
          simpa only [q, if_pos] using leftEntry_comp_self X q
        · have hz : Unitor.leftHomEntry x realUnitRowsData X q j =
              AtomHom.zero x.D _ _ := by
            simp [Unitor.leftHomEntry, Ne.symm hj]
          rw [hz, AtomHom.zero_comp
            realComputableShiftedRawDCT.laws.D]
          simpa only [q, hj, if_false]
      _ = _ := AtomHom.finSum_single
        realComputableShiftedRawDCT.laws.D q.right _
  · have hqq' : q.right ≠ q'.right := by
      intro h
      exact hik (leftIndex_right_injective X i k h)
    dsimp [q, q'] at hqq' ⊢
    unfold Hom.comp Unitor.leftHom Unitor.leftInv
    rw [show Hom.id x.D (Tensor.obj x.D x.C Unitor.unit X) i k =
        AtomHom.zero x.D _ _ by simp [Hom.id, hik]]
    change AtomHom.finSum X.size (fun j =>
        AtomHom.comp (Unitor.leftHomEntry x realUnitRowsData X q j)
          (Unitor.leftInvEntry x realUnitRowsData X j q')) =
      AtomHom.zero x.D _ _
    rw [AtomHom.finSum_congr (g := fun _ => AtomHom.zero x.D _ _)]
    · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
    · intro j
      by_cases hj : j = q.right
      · have hj' : j ≠ q'.right := by
          intro h'
          exact hqq' (hj.symm.trans h')
        have hz : Unitor.leftInvEntry x realUnitRowsData X j q' =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.leftInvEntry, hj']
        rw [hz, AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
      · have hz : Unitor.leftHomEntry x realUnitRowsData X q j =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.leftHomEntry, Ne.symm hj]
        rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]

/-- The stored inverse left unitor followed by the forward map is the
identity on `X`. -/
theorem realLeftUnitor_inv_hom (X : Obj) :
    Hom.comp (Unitor.leftInv x realUnitRowsData X)
        (Unitor.leftHom x realUnitRowsData X) =
      Hom.id x.D X := by
  apply Hom.ext
  intro i k
  by_cases hik : i = k
  · subst k
    obtain ⟨p, hp⟩ := leftUnitSlot_exists X i
    let q := (Tensor.slots x.D x.C Unitor.unit X).get p
    have hqright : q.right = i := by
      change ((Tensor.slots x.D x.C Unitor.unit X).get p).right = i
      exact (congrArg Tensor.Slot.right hp).trans rfl
    unfold Hom.comp Unitor.leftInv Unitor.leftHom
    rw [show Hom.id x.D X i i = AtomHom.id x.D (X.atom i) by
      simp [Hom.id]]
    change AtomHom.finSum (Tensor.obj x.D x.C Unitor.unit X).size
        (fun j => AtomHom.comp
          (Unitor.leftInvEntry x realUnitRowsData X i
            ((Tensor.slots x.D x.C Unitor.unit X).get j))
          (Unitor.leftHomEntry x realUnitRowsData X
            ((Tensor.slots x.D x.C Unitor.unit X).get j) i)) =
      AtomHom.id x.D (X.atom i)
    calc
      _ = AtomHom.finSum (Tensor.obj x.D x.C Unitor.unit X).size
          (fun j => if j = p then AtomHom.id x.D (X.atom i)
            else AtomHom.zero x.D _ _) := by
        apply AtomHom.finSum_congr
        intro j
        by_cases hj : j = p
        · subst j
          simp only [if_pos]
          change AtomHom.comp (Unitor.leftInvEntry x realUnitRowsData X i q)
              (Unitor.leftHomEntry x realUnitRowsData X q i) =
            AtomHom.id x.D (X.atom i)
          rw [← hqright]
          exact leftEntry_reverse_comp_self X q
        · have hright :
            ((Tensor.slots x.D x.C Unitor.unit X).get j).right ≠ i := by
            intro h
            have hjp := leftIndex_right_injective X j p
              (h.trans hqright.symm)
            exact hj hjp
          have hz : Unitor.leftInvEntry x realUnitRowsData X i
              ((Tensor.slots x.D x.C Unitor.unit X).get j) =
              AtomHom.zero x.D _ _ := by
            unfold Unitor.leftInvEntry
            simp only [dif_neg (Ne.symm hright)]
          rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
          simp only [hj, if_false]
      _ = _ := AtomHom.finSum_single
        realComputableShiftedRawDCT.laws.D p _
  · unfold Hom.comp Unitor.leftInv Unitor.leftHom
    rw [show Hom.id x.D X i k = AtomHom.zero x.D _ _ by
      simp [Hom.id, hik]]
    change AtomHom.finSum (Tensor.obj x.D x.C Unitor.unit X).size
        (fun j => AtomHom.comp
          (Unitor.leftInvEntry x realUnitRowsData X i
            ((Tensor.slots x.D x.C Unitor.unit X).get j))
          (Unitor.leftHomEntry x realUnitRowsData X
            ((Tensor.slots x.D x.C Unitor.unit X).get j) k)) =
      AtomHom.zero x.D _ _
    rw [AtomHom.finSum_congr (g := fun _ => AtomHom.zero x.D _ _)]
    · exact AtomHom.finSum_zero realComputableShiftedRawDCT.laws.D _
    · intro j
      let q := (Tensor.slots x.D x.C Unitor.unit X).get j
      by_cases hi : i = q.right
      · have hk : q.right ≠ k := by
          intro h
          exact hik (hi.trans h)
        have hz : Unitor.leftHomEntry x realUnitRowsData X q k =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.leftHomEntry, hk]
        rw [hz, AtomHom.comp_zero realComputableShiftedRawDCT.laws.D]
      · have hz : Unitor.leftInvEntry x realUnitRowsData X i q =
            AtomHom.zero x.D _ _ := by
          simp [Unitor.leftInvEntry, hi]
        rw [hz, AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]

/-! ## Evenness of the left unitor from the stored connector grading -/

private theorem rowParity_castIndex
    {a b a' b' : ZMod 8} (ha : a = a') (hb : b = b')
    (r : x.C.Index a b) :
    x.C.rowParity a' b' (Associator.castIndex x ha hb r) =
      x.C.rowParity a b r := by
  subst a'
  subst b'
  rfl

private theorem leftAssociatedUnitParity_zero (a : ZMod 8)
    (r : x.C.Index (0 + 0) a) :
    x.C.rowParity (0 + 0) a r = 0 := by
  let r' := Associator.castIndex x (zero_add 0) rfl r
  have hr' : r' = realUnitRowsData.left a :=
    realUnitRowsLaws.left_unique a r'
  have heven : x.C.rowParity 0 a r' = 0 := by
    rw [hr']
    exact realUnitRowsLaws.left_even a
  exact (rowParity_castIndex (zero_add 0) rfl r).symm.trans heven

private theorem leftHomCoefficient_even (a : ZMod 8)
    (r : x.C.Index 0 a) :
    (x.D.algebra a).MemGrade 0
      (Unitor.leftHomCoefficient x realUnitRowsData a r) := by
  let rightABC := Associator.castIndex x rfl (zero_add a).symm r
  let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
  have hraw := RealAssociatorLaws.realInvCoefficient_memGrade 0 0 a
    r rightABC (realUnitRowsData.left 0) leftABC
  have hraw0 : (x.D.algebra (0 + 0 + a)).MemGrade 0
      (Associator.invCoefficient x 0 0 a r rightABC
        (realUnitRowsData.left 0) leftABC) := by
    simpa only [zero_add, realUnitRowsLaws.left_unique,
      realUnitRowsLaws.left_even,
      leftAssociatedUnitParity_zero] using hraw
  unfold Unitor.leftHomCoefficient Unitor.castUnitTriple
  apply cast_algebra_memGrade_of_label_eq x.D
    realComputableShiftedRawDCT.laws.D (by simp only [zero_add])
  simpa only [rightABC, leftABC] using hraw0

private theorem leftInvCoefficient_even (a : ZMod 8)
    (r : x.C.Index 0 a) :
    (x.D.algebra a).MemGrade 0
      (Unitor.leftInvCoefficient x realUnitRowsData a r) := by
  let rightABC := Associator.castIndex x rfl (zero_add a).symm r
  let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
  have hraw := RealAssociatorLaws.realHomCoefficient_memGrade 0 0 a
    (realUnitRowsData.left 0) leftABC r rightABC
  have hraw0 : (x.D.algebra (0 + 0 + a)).MemGrade 0
      (Associator.homCoefficient x 0 0 a
        (realUnitRowsData.left 0) leftABC r rightABC) := by
    simpa only [zero_add, realUnitRowsLaws.left_unique,
      realUnitRowsLaws.left_even,
      leftAssociatedUnitParity_zero] using hraw
  unfold Unitor.leftInvCoefficient Unitor.castUnitTriple
  apply cast_algebra_memGrade_of_label_eq x.D
    realComputableShiftedRawDCT.laws.D (by simp only [zero_add])
  simpa only [rightABC, leftABC] using hraw0

private theorem leftHomEntry_even (X : Obj)
    (q : Tensor.Slot x.D x.C Unitor.unit X) (j : Fin X.size) :
    AtomHom.MemGrade 0 (Unitor.leftHomEntry x realUnitRowsData X q j) := by
  by_cases hj : q.right = j
  · subst j
    intro hLabel
    have hrow : x.C.rowParity 0 (X.atom q.right).label q.fusion = 0 := by
      rw [realUnitRowsLaws.left_unique _ q.fusion]
      exact realUnitRowsLaws.left_even _
    have hdegree : 0 +
        (Tensor.slotAtom x.D x.C Unitor.unit X q).shift +
        (X.atom q.right).shift = 0 := by
      change 0 + (0 + (X.atom q.right).shift +
          x.C.rowParity 0 (X.atom q.right).label q.fusion) +
        (X.atom q.right).shift = 0
      rw [hrow]
      simpa only [add_zero, zero_add] using
        zmod2_add_self (X.atom q.right).shift
    rw [hdegree]
    simp [Unitor.leftHomEntry]
    apply cast_algebra_memGrade_of_label_eq x.D
      realComputableShiftedRawDCT.laws.D
      (a := (X.atom q.right).label)
      (b := (Tensor.slotAtom x.D x.C Unitor.unit X q).label)
      (zero_add _).symm
    exact leftHomCoefficient_even (X.atom q.right).label q.fusion
  · rw [show Unitor.leftHomEntry x realUnitRowsData X q j =
        AtomHom.zero x.D _ _ by
      unfold Unitor.leftHomEntry
      simp only [dif_neg hj]]
    exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0

private theorem leftInvEntry_even (X : Obj) (i : Fin X.size)
    (q : Tensor.Slot x.D x.C Unitor.unit X) :
    AtomHom.MemGrade 0 (Unitor.leftInvEntry x realUnitRowsData X i q) := by
  by_cases hi : i = q.right
  · subst i
    intro hLabel
    have hrow : x.C.rowParity 0 (X.atom q.right).label q.fusion = 0 := by
      rw [realUnitRowsLaws.left_unique _ q.fusion]
      exact realUnitRowsLaws.left_even _
    have hdegree : 0 + (X.atom q.right).shift +
        (Tensor.slotAtom x.D x.C Unitor.unit X q).shift = 0 := by
      change 0 + (X.atom q.right).shift +
        (0 + (X.atom q.right).shift +
          x.C.rowParity 0 (X.atom q.right).label q.fusion) = 0
      rw [hrow]
      simpa only [add_zero, zero_add] using
        zmod2_add_self (X.atom q.right).shift
    rw [hdegree]
    simp [Unitor.leftInvEntry]
    exact leftInvCoefficient_even (X.atom q.right).label q.fusion
  · rw [show Unitor.leftInvEntry x realUnitRowsData X i q =
        AtomHom.zero x.D _ _ by
      unfold Unitor.leftInvEntry
      simp only [dif_neg hi]]
    exact AtomHom.zero_memGrade realComputableShiftedRawDCT.laws.D 0

/-- The forward real left unitor is even. -/
theorem realLeftUnitor_hom_even (X : Obj) :
    Hom.MemGrade 0 (Unitor.leftHom x realUnitRowsData X) := by
  intro i j
  exact leftHomEntry_even X
    ((Tensor.slots x.D x.C Unitor.unit X).get i) j

/-- The inverse real left unitor is even. -/
theorem realLeftUnitor_inv_even (X : Obj) :
    Hom.MemGrade 0 (Unitor.leftInv x realUnitRowsData X) := by
  intro i j
  exact leftInvEntry_even X i
    ((Tensor.slots x.D x.C Unitor.unit X).get j)

/-! ## Unit-face tensor action and left-unitor centrality -/

private theorem routeRowTwist_one_at (a : ZMod 8) (p : ZMod 2) :
    RawDCT.routeRowTwist x.D a p (x.D.algebra a).one =
      (x.D.algebra a).one :=
  RawDCT.routeRowTwist_one (x.D.algebra a)
    (realComputableShiftedRawDCT.laws.D.algebra_laws a) p

private theorem routeRowTwist_zero_at (a : ZMod 8)
    (u : (x.D.algebra a).carrier) :
    RawDCT.routeRowTwist x.D a 0 u = u :=
  RawDCT.routeRowTwist_zeroParity (x.D.algebra a)
    (realComputableShiftedRawDCT.laws.D.algebra_laws a) u

private theorem tensorCoefficient_left_unit (a : ZMod 8)
    (t t' : ZMod 2) (source target : x.C.Index 0 a)
    (y : (x.D.algebra a).carrier) :
    Tensor.coefficient x.D x.C 0 a 0 t t' source target
        (x.D.algebra 0).one y =
      cast (congrArg (fun u : ZMod 8 => (x.D.algebra u).carrier)
        (zero_add a).symm) y := by
  rw [realUnitRowsLaws.left_unique a source,
    realUnitRowsLaws.left_unique a target]
  unfold Tensor.coefficient
  rw [zero_mul, shiftParitySign_zero]
  rw [routeRowTwist_one_at, routeRowTwist_zero_at]
  rw [realComputableShifted_leftCoeff_left_unit]
  exact (realComputableShiftedRawDCT.laws.D.algebra_laws _).one_smul _

private theorem tensorCoefficient_right_unit (a : ZMod 8)
    (s : ZMod 2) (source target : x.C.Index a 0)
    (u : (x.D.algebra a).carrier) :
    Tensor.coefficient x.D x.C a 0 s 0 0 source target u
        (x.D.algebra 0).one =
      cast (congrArg (fun v : ZMod 8 => (x.D.algebra v).carrier)
        (add_zero a).symm) u := by
  rw [realUnitRowsLaws.right_unique a source,
    realUnitRowsLaws.right_unique a target]
  unfold Tensor.coefficient
  rw [zero_add, mul_zero, shiftParitySign_zero]
  rw [routeRowTwist_zero_at, routeRowTwist_one_at]
  rw [realComputableShifted_leftCoeff_right_unit]
  exact (realComputableShiftedRawDCT.laws.D.algebra_laws _).one_smul _

private def castToUnitTriple (a : ZMod 8) :
    (x.D.algebra a).carrier → (x.D.algebra (0 + 0 + a)).carrier :=
  cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
    (by simp : 0 + 0 + a = a)).symm

private theorem castToUnitTriple_add (a : ZMod 8)
    (u v : (x.D.algebra a).carrier) :
    castToUnitTriple a ((x.D.algebra a).add u v) =
      (x.D.algebra (0 + 0 + a)).add
        (castToUnitTriple a u) (castToUnitTriple a v) := by
  apply cast_algebra_add_of_label_eq x.D
    (by simp only [zero_add] : a = 0 + 0 + a)

private theorem castUnitTriple_castToUnitTriple (a : ZMod 8)
    (u : (x.D.algebra a).carrier) :
    Unitor.castUnitTriple x a (castToUnitTriple a u) = u := by
  simp only [Unitor.castUnitTriple, castToUnitTriple]
  rw [cast_cast_eq]
  congr

private theorem castUnitTriple_mul (a : ZMod 8)
    (u v : (x.D.algebra (0 + 0 + a)).carrier) :
    Unitor.castUnitTriple x a
        ((x.D.algebra (0 + 0 + a)).mul u v) =
      (x.D.algebra a).mul (Unitor.castUnitTriple x a u)
        (Unitor.castUnitTriple x a v) := by
  unfold Unitor.castUnitTriple
  apply cast_algebra_mul_of_label_eq x.D
    (by simp only [zero_add] : 0 + 0 + a = a)

private theorem leftRouteCoeff_unit (a : ZMod 8)
    (targetAB sourceAB : x.C.Index 0 0)
    (targetABC sourceABC : x.C.Index (0 + 0) a)
    (u : (x.D.algebra a).carrier) :
    RawDCT.leftRouteCoeff x.C 0 0 a targetAB targetABC
        sourceAB sourceABC (x.D.algebra 0).one
        (x.D.algebra 0).one u = castToUnitTriple a u := by
  rw [realUnitRowsLaws.left_unique 0 targetAB,
    realUnitRowsLaws.left_unique 0 sourceAB]
  unfold RawDCT.leftRouteCoeff
  rw [realComputableShifted_leftCoeff_left_unit]
  rw [realUnitRowsLaws.left_even, routeRowTwist_zero_at]
  rw [cast_algebra_one x.D (zero_add 0).symm]
  rw [leftCoeff_transport_first_to_zero x (0 + 0) a (zero_add 0)]
  rw [realUnitRowsLaws.left_unique a
      (Associator.castIndex x (zero_add 0) rfl targetABC),
    realUnitRowsLaws.left_unique a
      (Associator.castIndex x (zero_add 0) rfl sourceABC)]
  rw [cast_algebra_one x.D (zero_add 0)]
  rw [realComputableShifted_leftCoeff_left_unit]
  simp only [castToUnitTriple]
  rw [cast_cast_eq]

private theorem rightRouteCoeff_unit (a : ZMod 8)
    (targetBC sourceBC : x.C.Index 0 a)
    (targetABC sourceABC : x.C.Index 0 (0 + a))
    (u : (x.D.algebra a).carrier) :
    RawDCT.rightRouteCoeff x.C 0 0 a targetBC targetABC
        sourceBC sourceABC (x.D.algebra 0).one
        (x.D.algebra 0).one u = castToUnitTriple a u := by
  rw [realUnitRowsLaws.left_unique a targetBC,
    realUnitRowsLaws.left_unique a sourceBC,
    realUnitRowsLaws.left_unique (0 + a) targetABC,
    realUnitRowsLaws.left_unique (0 + a) sourceABC]
  unfold RawDCT.rightRouteCoeff
  rw [realUnitRowsLaws.left_even, routeRowTwist_zero_at]
  rw [realComputableShifted_leftCoeff_left_unit]
  rw [realComputableShifted_leftCoeff_left_unit]
  simp only [RawDCT.routeCastAssoc, castToUnitTriple]
  rw [cast_cast_eq, cast_cast_eq]

private theorem leftAssociatedIndex_eq (a : ZMod 8)
    (r s : x.C.Index (0 + 0) a) : r = s := by
  apply castIndex_injective x (zero_add 0) rfl
  exact (realUnitRowsLaws.left_unique a
      (Associator.castIndex x (zero_add 0) rfl r)).trans
    (realUnitRowsLaws.left_unique a
      (Associator.castIndex x (zero_add 0) rfl s)).symm

private theorem rightUnitOuterIndex_eq (a : ZMod 8)
    (r s : x.C.Index 0 (0 + a)) : r = s :=
  (realUnitRowsLaws.left_unique (0 + a) r).trans
    (realUnitRowsLaws.left_unique (0 + a) s).symm

private theorem rightLeftPureDelta_unit (a : ZMod 8)
    (r : x.C.Index 0 a) (u : (x.D.algebra a).carrier) :
    let rightABC := Associator.castIndex x rfl (zero_add a).symm r
    x.T.rightToCoord 0 0 a
        (x.T.rightRoute.leftPure 0 0 a
          (x.D.algebra 0).one (x.D.algebra 0).one u
          (x.T.rightOfCoord 0 0 a
            (Associator.rightDelta x 0 0 a r rightABC)))
        r rightABC = castToUnitTriple a u := by
  let rightABC := Associator.castIndex x rfl (zero_add a).symm r
  dsimp only
  rw [realComputableShiftedRawDCT.laws.T.right_toCoord_leftPure]
  dsimp only
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _) r
      (fun s => (realUnitRowsLaws.left_unique a s).trans
        (realUnitRowsLaws.left_unique a r).symm)]
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _) rightABC
      (fun s => rightUnitOuterIndex_eq a s rightABC)]
  rw [rightRouteCoeff_unit]
  rw [realComputableShiftedRawDCT.laws.T.right_toCoord_ofCoord]
  rw [Associator.rightDelta_source]
  exact (realComputableShiftedRawDCT.laws.D.algebra_laws _).mul_one _

private theorem leftLeftPureInvDelta_unit (a : ZMod 8)
    (r : x.C.Index 0 a) (u : (x.D.algebra a).carrier) :
    let rightABC := Associator.castIndex x rfl (zero_add a).symm r
    let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
    x.T.leftToCoord 0 0 a
        (x.T.leftRoute.leftPure 0 0 a
          (x.D.algebra 0).one (x.D.algebra 0).one u
          (x.T.inv 0 0 a
            (x.T.rightOfCoord 0 0 a
              (Associator.rightDelta x 0 0 a r rightABC))))
        (realUnitRowsData.left 0) leftABC =
      (x.D.algebra (0 + 0 + a)).mul (castToUnitTriple a u)
        (Associator.invCoefficient x 0 0 a r rightABC
          (realUnitRowsData.left 0) leftABC) := by
  let rightABC := Associator.castIndex x rfl (zero_add a).symm r
  let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
  dsimp only
  rw [realComputableShiftedRawDCT.laws.T.left_toCoord_leftPure]
  dsimp only
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _)
      (realUnitRowsData.left 0) (realUnitRowsLaws.left_unique 0)]
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _) leftABC
      (fun s => leftAssociatedIndex_eq a s leftABC)]
  rw [leftRouteCoeff_unit]
  rfl

private theorem invRightLeftPureDelta_unit (a : ZMod 8)
    (r : x.C.Index 0 a) (u : (x.D.algebra a).carrier) :
    let rightABC := Associator.castIndex x rfl (zero_add a).symm r
    let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
    x.T.leftToCoord 0 0 a
        (x.T.inv 0 0 a
          (x.T.rightRoute.leftPure 0 0 a
            (x.D.algebra 0).one (x.D.algebra 0).one u
            (x.T.rightOfCoord 0 0 a
              (Associator.rightDelta x 0 0 a r rightABC))))
        (realUnitRowsData.left 0) leftABC =
      (x.D.algebra (0 + 0 + a)).mul
        (Associator.invCoefficient x 0 0 a r rightABC
          (realUnitRowsData.left 0) leftABC)
        (castToUnitTriple a u) := by
  let rightABC := Associator.castIndex x rfl (zero_add a).symm r
  let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
  dsimp only
  rw [Associator.inv_toCoord_eq_matrix x
    realComputableShiftedRawDCT.laws]
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _) r
      (fun s => (realUnitRowsLaws.left_unique a s).trans
        (realUnitRowsLaws.left_unique a r).symm)]
  rw [rawFinSum_eq_single_of_unique _
      (realComputableShiftedRawDCT.laws.D.algebra_laws _) rightABC
      (fun s => rightUnitOuterIndex_eq a s rightABC)]
  rw [rightLeftPureDelta_unit]

private theorem shiftedConnectorParity_zero (a b c : ZMod 8) :
    x.T.parity a b c = 0 := by
  exact realComputableShiftedRawDCT_parity_eq_zero _ _ _

private theorem leftRawInvCoefficient_commutes_homogeneous (a : ZMod 8)
    (r : x.C.Index 0 a) (k : ZMod 2)
    (u : (x.D.algebra a).carrier)
    (hu : (x.D.algebra a).MemGrade k u) :
    let rightABC := Associator.castIndex x rfl (zero_add a).symm r
    let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
    (x.D.algebra (0 + 0 + a)).mul
        (Associator.invCoefficient x 0 0 a r rightABC
          (realUnitRowsData.left 0) leftABC)
        (castToUnitTriple a u) =
      (x.D.algebra (0 + 0 + a)).mul (castToUnitTriple a u)
        (Associator.invCoefficient x 0 0 a r rightABC
          (realUnitRowsData.left 0) leftABC) := by
  let rightABC := Associator.castIndex x rfl (zero_add a).symm r
  let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
  let m := x.T.rightOfCoord 0 0 a
    (Associator.rightDelta x 0 0 a r rightABC)
  have h := congrArg
    (fun n => x.T.leftToCoord 0 0 a n
      (realUnitRowsData.left 0) leftABC)
    (realComputableShiftedRawDCT.laws.T.inv_left 0 0 a 0 0 k
      (x.D.algebra 0).one (x.D.algebra 0).one u m
      (realComputableShiftedRawDCT.laws.D.algebra_laws 0).one_mem
      (realComputableShiftedRawDCT.laws.D.algebra_laws 0).one_mem hu)
  rw [shiftedConnectorParity_zero, zero_mul,
    RawDCT.shiftParitySign_zero,
    realComputableShiftedRawDCT.laws.T.left_route_laws.one_smul] at h
  dsimp only [m] at h
  rw [invRightLeftPureDelta_unit, leftLeftPureInvDelta_unit] at h
  simpa only [rightABC, leftABC] using h

private theorem leftRawInvCoefficient_commutes (a : ZMod 8)
    (r : x.C.Index 0 a) (u : (x.D.algebra a).carrier) :
    let rightABC := Associator.castIndex x rfl (zero_add a).symm r
    let leftABC := Associator.castIndex x (zero_add 0).symm rfl r
    (x.D.algebra (0 + 0 + a)).mul
        (Associator.invCoefficient x 0 0 a r rightABC
          (realUnitRowsData.left 0) leftABC)
        (castToUnitTriple a u) =
      (x.D.algebra (0 + 0 + a)).mul (castToUnitTriple a u)
        (Associator.invCoefficient x 0 0 a r rightABC
          (realUnitRowsData.left 0) leftABC) := by
  let u₀ := (x.D.algebra a).component 0 u
  let u₁ := (x.D.algebra a).component 1 u
  have hu₀ : (x.D.algebra a).MemGrade 0 u₀ :=
    (realComputableShiftedRawDCT.laws.D.algebra_laws a).component_idem 0 u
  have hu₁ : (x.D.algebra a).MemGrade 1 u₁ :=
    (realComputableShiftedRawDCT.laws.D.algebra_laws a).component_idem 1 u
  have hsum : (x.D.algebra a).add u₀ u₁ = u := by
    simpa only [u₀, u₁, zero_add] using
      (realComputableShiftedRawDCT.laws.D.algebra_laws a).component_complement 0 u
  dsimp only
  rw [← hsum, castToUnitTriple_add]
  rw [(realComputableShiftedRawDCT.laws.D.algebra_laws _).mul_add,
    (realComputableShiftedRawDCT.laws.D.algebra_laws _).add_mul]
  rw [leftRawInvCoefficient_commutes_homogeneous a r 0 u₀ hu₀,
    leftRawInvCoefficient_commutes_homogeneous a r 1 u₁ hu₁]

private theorem leftHomCoefficient_commutes (a : ZMod 8)
    (r : x.C.Index 0 a) (u : (x.D.algebra a).carrier) :
    (x.D.algebra a).mul
        (Unitor.leftHomCoefficient x realUnitRowsData a r) u =
      (x.D.algebra a).mul u
        (Unitor.leftHomCoefficient x realUnitRowsData a r) := by
  have h := congrArg (Unitor.castUnitTriple x a)
    (leftRawInvCoefficient_commutes a r u)
  rw [castUnitTriple_mul, castUnitTriple_mul,
    castUnitTriple_castToUnitTriple] at h
  unfold Unitor.leftHomCoefficient
  convert h using 1

private theorem leftHomCoefficient_transport {a b : ZMod 8}
    (hab : a = b) (r : x.C.Index 0 a) (s : x.C.Index 0 b) :
    cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier) hab)
        (Unitor.leftHomCoefficient x realUnitRowsData a r) =
      Unitor.leftHomCoefficient x realUnitRowsData b s := by
  subst b
  have hrs : r = s :=
    (realUnitRowsLaws.left_unique a r).trans
      (realUnitRowsLaws.left_unique a s).symm
  subst s
  congr

/-! ## Naturality of the left unitor -/

private theorem leftNaturalityEntry {X Y : Obj} (f : Hom x.D X Y)
    (q : Tensor.Slot x.D x.C Unitor.unit X)
    (q' : Tensor.Slot x.D x.C Unitor.unit Y) :
    AtomHom.comp
        (Tensor.entry x.D x.C (Hom.id x.D Unitor.unit) f q q')
        (Unitor.leftHomEntry x realUnitRowsData Y q' q'.right) =
      AtomHom.comp
        (Unitor.leftHomEntry x realUnitRowsData X q q.right)
        (f q.right q'.right) := by
  rcases q with ⟨qi, qj, qr⟩
  have hqi : qi = (⟨0, Nat.zero_lt_one⟩ : Fin Unitor.unit.size) := by
    apply Fin.ext
    have hlt : qi.val < 1 := by
      simpa [Unitor.unit, Obj.singleton, Obj.size] using qi.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  subst qi
  have hqr : qr = realUnitRowsData.left (X.atom qj).label :=
    realUnitRowsLaws.left_unique _ qr
  subst qr
  rcases q' with ⟨qi', qj', qr'⟩
  have hqi' : qi' = (⟨0, Nat.zero_lt_one⟩ : Fin Unitor.unit.size) := by
    apply Fin.ext
    have hlt : qi'.val < 1 := by
      simpa [Unitor.unit, Obj.singleton, Obj.size] using qi'.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  subst qi'
  have hqr' : qr' = realUnitRowsData.left (Y.atom qj').label :=
    realUnitRowsLaws.left_unique _ qr'
  subst qr'
  let q := leftUnitSlot X qj
  let q' := leftUnitSlot Y qj'
  change AtomHom.comp
      (Tensor.entry x.D x.C (Hom.id x.D Unitor.unit) f q q')
      (Unitor.leftHomEntry x realUnitRowsData Y q' q'.right) =
    AtomHom.comp
      (Unitor.leftHomEntry x realUnitRowsData X q q.right)
      (f q.right q'.right)
  apply AtomHom.ext
  intro hLabel
  have hA : (X.atom qj).label = (Y.atom qj').label := by
    change 0 + (X.atom qj).label = (Y.atom qj').label at hLabel
    simpa only [zero_add] using hLabel
  have hAq : (X.atom q.right).label = (Y.atom q'.right).label := by
    simpa [q, q', leftUnitSlot, Tensor.Slot.right] using hA
  have hAraw : (X.snd qj).1 = (Y.snd qj').1 := hA
  have hQQ : (Tensor.slotAtom x.D x.C Unitor.unit X q).label =
      (Tensor.slotAtom x.D x.C Unitor.unit Y q').label := by
    change 0 + (X.atom qj).label = 0 + (Y.atom qj').label
    rw [hA]
  have hQY : (Tensor.slotAtom x.D x.C Unitor.unit Y q').label =
      (Y.atom q'.right).label := by
    change 0 + (Y.atom q'.right).label = (Y.atom q'.right).label
    exact zero_add _
  have hQX : (Tensor.slotAtom x.D x.C Unitor.unit X q).label =
      (X.atom q.right).label := by
    change 0 + (X.atom q.right).label = (X.atom q.right).label
    exact zero_add _
  have hh : hLabel = hQQ.trans hQY := Subsingleton.elim _ _
  cases hh
  rw [AtomHom.coeff_comp _ _ hQQ hQY]
  have hp : hQQ.trans hQY = hQX.trans hAq := Subsingleton.elim _ _
  rw [hp]
  rw [AtomHom.coeff_comp _ _ hQX hAq]
  let fAtSlot :
      (x.D.algebra (Tensor.slotAtom x.D x.C Unitor.unit X q).label).carrier :=
    cast (congrArg (fun a : ZMod 8 => (x.D.algebra a).carrier) hQX).symm
      ((f q.right q'.right).coeff hAq)
  have hTensor :
      (Tensor.entry x.D x.C (Hom.id x.D Unitor.unit) f q q').coeff hQQ =
        fAtSlot := by
    simp [q, q', leftUnitSlot, Tensor.entry, hAraw,
      Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion,
      Hom.id, Unitor.unit, Obj.singleton, Obj.atom, Atom.label, Atom.shift,
      tensorCoefficient_left_unit, fAtSlot]
    congr
  rw [hTensor]
  simp [Unitor.leftHomEntry]
  have hLCoeff :
      cast (congrArg (fun a : ZMod 8 => (x.D.algebra a).carrier)
          (hQQ.trans hQY)).symm
          (Unitor.leftHomCoefficient x realUnitRowsData
            (Y.atom q'.right).label q'.fusion) =
        cast (congrArg (fun a : ZMod 8 => (x.D.algebra a).carrier) hQX).symm
          (Unitor.leftHomCoefficient x realUnitRowsData
            (X.atom q.right).label q.fusion) := by
    rw [← leftHomCoefficient_transport hAq q.fusion q'.fusion]
    rw [cast_cast_eq]
  rw [hLCoeff]
  have hc := congrArg
    (fun z => cast
      (congrArg (fun a : ZMod 8 => (x.D.algebra a).carrier) hQX).symm z)
    (leftHomCoefficient_commutes (X.atom q.right).label q.fusion
      ((f q.right q'.right).coeff hAq))
  rw [cast_algebra_mul_of_label_eq x.D hQX.symm,
    cast_algebra_mul_of_label_eq x.D hQX.symm] at hc
  simpa only [fAtSlot] using hc

/-- Naturality of the canonical real left unitor. -/
theorem realLeftUnitor_naturality {X Y : Obj} (f : Hom x.D X Y) :
    Hom.comp (Tensor.hom x.D x.C (Hom.id x.D Unitor.unit) f)
        (Unitor.leftHom x realUnitRowsData Y) =
      Hom.comp (Unitor.leftHom x realUnitRowsData X) f := by
  apply Hom.ext
  intro i k
  let q := (Tensor.slots x.D x.C Unitor.unit X).get i
  obtain ⟨p, hp⟩ := leftUnitSlot_exists Y k
  let q' := (Tensor.slots x.D x.C Unitor.unit Y).get p
  have hq'right : q'.right = k := by
    change ((Tensor.slots x.D x.C Unitor.unit Y).get p).right = k
    exact (congrArg Tensor.Slot.right hp).trans rfl
  unfold Hom.comp Tensor.hom Unitor.leftHom
  change AtomHom.finSum (Tensor.obj x.D x.C Unitor.unit Y).size
      (fun j => AtomHom.comp
        (Tensor.entry x.D x.C (Hom.id x.D Unitor.unit) f q
          ((Tensor.slots x.D x.C Unitor.unit Y).get j))
        (Unitor.leftHomEntry x realUnitRowsData Y
          ((Tensor.slots x.D x.C Unitor.unit Y).get j) k)) =
    AtomHom.finSum X.size (fun j => AtomHom.comp
      (Unitor.leftHomEntry x realUnitRowsData X q j) (f j k))
  calc
    _ = AtomHom.comp
        (Tensor.entry x.D x.C (Hom.id x.D Unitor.unit) f q q')
        (Unitor.leftHomEntry x realUnitRowsData Y q' k) := by
      rw [AtomHom.finSum_congr (g := fun j =>
          if j = p then
            AtomHom.comp
              (Tensor.entry x.D x.C (Hom.id x.D Unitor.unit) f q q')
              (Unitor.leftHomEntry x realUnitRowsData Y q' k)
          else AtomHom.zero x.D _ _)]
      · exact AtomHom.finSum_single
          realComputableShiftedRawDCT.laws.D p _
      · intro j
        by_cases hj : j = p
        · subst j
          simp only [q', if_pos]
        · have hright :
              ((Tensor.slots x.D x.C Unitor.unit Y).get j).right ≠ k := by
            intro h
            have hjp := leftIndex_right_injective Y j p
              (h.trans hq'right.symm)
            exact hj hjp
          have hz : Unitor.leftHomEntry x realUnitRowsData Y
              ((Tensor.slots x.D x.C Unitor.unit Y).get j) k =
              AtomHom.zero x.D _ _ := by
            unfold Unitor.leftHomEntry
            simp only [dif_neg hright]
          rw [hz, AtomHom.comp_zero
            realComputableShiftedRawDCT.laws.D]
          simp only [hj, if_false]
    _ = AtomHom.comp
        (Unitor.leftHomEntry x realUnitRowsData X q q.right)
        (f q.right k) := by
      rw [← hq'right]
      exact leftNaturalityEntry f q q'
    _ = _ := by
      rw [AtomHom.finSum_congr (g := fun j =>
          if j = q.right then
            AtomHom.comp
              (Unitor.leftHomEntry x realUnitRowsData X q q.right)
              (f q.right k)
          else AtomHom.zero x.D _ _)]
      · exact (AtomHom.finSum_single
          realComputableShiftedRawDCT.laws.D q.right _).symm
      · intro j
        by_cases hj : j = q.right
        · subst j
          simp only [if_pos]
        · have hz : Unitor.leftHomEntry x realUnitRowsData X q j =
              AtomHom.zero x.D _ _ := by
            unfold Unitor.leftHomEntry
            simp only [dif_neg (Ne.symm hj)]
          rw [hz, AtomHom.zero_comp
            realComputableShiftedRawDCT.laws.D]
          simp only [hj, if_false]

/-! ## Naturality of the right unitor -/

private theorem rightNaturalityEntry {X Y : Obj} (f : Hom x.D X Y)
    (q : Tensor.Slot x.D x.C X Unitor.unit)
    (q' : Tensor.Slot x.D x.C Y Unitor.unit) :
    AtomHom.comp
        (Tensor.entry x.D x.C f (Hom.id x.D Unitor.unit) q q')
        (Unitor.rightHomEntry x Y q' q'.left) =
      AtomHom.comp (Unitor.rightHomEntry x X q q.left)
        (f q.left q'.left) := by
  rcases q with ⟨qi, qj, qr⟩
  have hqj : qj = (⟨0, Nat.zero_lt_one⟩ : Fin Unitor.unit.size) := by
    apply Fin.ext
    have hlt : qj.val < 1 := by
      simpa [Unitor.unit, Obj.singleton, Obj.size] using qj.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  subst qj
  have hqr : qr = realUnitRowsData.right (X.atom qi).label :=
    realUnitRowsLaws.right_unique _ qr
  subst qr
  rcases q' with ⟨qi', qj', qr'⟩
  have hqj' : qj' = (⟨0, Nat.zero_lt_one⟩ : Fin Unitor.unit.size) := by
    apply Fin.ext
    have hlt : qj'.val < 1 := by
      simpa [Unitor.unit, Obj.singleton, Obj.size] using qj'.isLt
    exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)
  subst qj'
  have hqr' : qr' = realUnitRowsData.right (Y.atom qi').label :=
    realUnitRowsLaws.right_unique _ qr'
  subst qr'
  let q := rightUnitSlot X qi
  let q' := rightUnitSlot Y qi'
  change AtomHom.comp
      (Tensor.entry x.D x.C f (Hom.id x.D Unitor.unit) q q')
      (Unitor.rightHomEntry x Y q' q'.left) =
    AtomHom.comp (Unitor.rightHomEntry x X q q.left)
      (f q.left q'.left)
  apply AtomHom.ext
  intro hLabel
  have hUnit : q.right = q'.right := rfl
  have hA : (X.atom qi).label = (Y.atom qi').label := by
    change (X.atom qi).label + 0 = (Y.atom qi').label at hLabel
    simpa only [add_zero] using hLabel
  have hAq : (X.atom q.left).label = (Y.atom q'.left).label := by
    simpa [q, q', rightUnitSlot, Tensor.Slot.left] using hA
  have hAraw : (X.snd qi).1 = (Y.snd qi').1 := hA
  have hQQ : (Tensor.slotAtom x.D x.C X Unitor.unit q).label =
      (Tensor.slotAtom x.D x.C Y Unitor.unit q').label := by
    change (X.atom qi).label + 0 = (Y.atom qi').label + 0
    rw [hA]
  have hQY : (Tensor.slotAtom x.D x.C Y Unitor.unit q').label =
      (Y.atom q'.left).label := by
    change (Y.atom q'.left).label + 0 = (Y.atom q'.left).label
    exact add_zero _
  have hQX : (Tensor.slotAtom x.D x.C X Unitor.unit q).label =
      (X.atom q.left).label := by
    change (X.atom q.left).label + 0 = (X.atom q.left).label
    exact add_zero _
  have hh : hLabel = hQQ.trans hQY := Subsingleton.elim _ _
  cases hh
  rw [AtomHom.coeff_comp _ _ hQQ hQY]
  have hp : hQQ.trans hQY = hQX.trans hAq := Subsingleton.elim _ _
  rw [hp]
  rw [AtomHom.coeff_comp _ _ hQX hAq]
  let fAtSlot :
      (x.D.algebra (Tensor.slotAtom x.D x.C X Unitor.unit q).label).carrier :=
    cast (congrArg (fun a : ZMod 8 => (x.D.algebra a).carrier) hQX).symm
      ((f q.left q'.left).coeff hAq)
  have hTensor :
      (Tensor.entry x.D x.C f (Hom.id x.D Unitor.unit) q q').coeff hQQ =
        fAtSlot := by
    simp [q, q', rightUnitSlot, Tensor.entry, hAraw,
      Tensor.Slot.left, Tensor.Slot.right, Tensor.Slot.fusion,
      Hom.id, Unitor.unit, Obj.singleton, Obj.atom, Atom.label, Atom.shift,
      tensorCoefficient_right_unit, fAtSlot]
    congr
  rw [hTensor]
  simp [Unitor.rightHomEntry]
  rw [cast_algebra_one_symm x.D (hQQ.trans hQY),
    cast_algebra_one_symm x.D hQX]
  simpa only [fAtSlot] using
    ((realComputableShiftedRawDCT.laws.D.algebra_laws _).one_mul fAtSlot).trans
      ((realComputableShiftedRawDCT.laws.D.algebra_laws _).mul_one fAtSlot).symm

/-- Naturality of the canonical real right unitor. -/
theorem realRightUnitor_naturality {X Y : Obj} (f : Hom x.D X Y) :
    Hom.comp (Tensor.hom x.D x.C f (Hom.id x.D Unitor.unit))
        (Unitor.rightHom x Y) =
      Hom.comp (Unitor.rightHom x X) f := by
  apply Hom.ext
  intro i k
  let q := (Tensor.slots x.D x.C X Unitor.unit).get i
  obtain ⟨p, hp⟩ := rightUnitSlot_exists Y k
  let q' := (Tensor.slots x.D x.C Y Unitor.unit).get p
  have hq'left : q'.left = k := by
    change ((Tensor.slots x.D x.C Y Unitor.unit).get p).left = k
    exact (congrArg Tensor.Slot.left hp).trans rfl
  unfold Hom.comp Tensor.hom Unitor.rightHom
  change AtomHom.finSum (Tensor.obj x.D x.C Y Unitor.unit).size
      (fun j => AtomHom.comp
        (Tensor.entry x.D x.C f (Hom.id x.D Unitor.unit) q
          ((Tensor.slots x.D x.C Y Unitor.unit).get j))
        (Unitor.rightHomEntry x Y
          ((Tensor.slots x.D x.C Y Unitor.unit).get j) k)) =
    AtomHom.finSum X.size (fun j => AtomHom.comp
      (Unitor.rightHomEntry x X q j) (f j k))
  calc
    _ = AtomHom.comp
        (Tensor.entry x.D x.C f (Hom.id x.D Unitor.unit) q q')
        (Unitor.rightHomEntry x Y q' k) := by
      rw [AtomHom.finSum_congr (g := fun j =>
          if j = p then
            AtomHom.comp
              (Tensor.entry x.D x.C f (Hom.id x.D Unitor.unit) q q')
              (Unitor.rightHomEntry x Y q' k)
          else AtomHom.zero x.D _ _)]
      · exact AtomHom.finSum_single
          realComputableShiftedRawDCT.laws.D p _
      · intro j
        by_cases hj : j = p
        · subst j
          simp only [q', if_pos]
        · have hleft :
              ((Tensor.slots x.D x.C Y Unitor.unit).get j).left ≠ k := by
            intro h
            have hjp := rightIndex_left_injective Y j p
              (h.trans hq'left.symm)
            exact hj hjp
          have hz : Unitor.rightHomEntry x Y
              ((Tensor.slots x.D x.C Y Unitor.unit).get j) k =
              AtomHom.zero x.D _ _ := by
            unfold Unitor.rightHomEntry
            simp only [dif_neg hleft]
          rw [hz, AtomHom.comp_zero
            realComputableShiftedRawDCT.laws.D]
          simp only [hj, if_false]
    _ = AtomHom.comp (Unitor.rightHomEntry x X q q.left)
        (f q.left k) := by
      rw [← hq'left]
      exact rightNaturalityEntry f q q'
    _ = _ := by
      rw [AtomHom.finSum_congr (g := fun j =>
          if j = q.left then
            AtomHom.comp (Unitor.rightHomEntry x X q q.left)
              (f q.left k)
          else AtomHom.zero x.D _ _)]
      · exact (AtomHom.finSum_single
          realComputableShiftedRawDCT.laws.D q.left _).symm
      · intro j
        by_cases hj : j = q.left
        · subst j
          simp only [if_pos]
        · have hz : Unitor.rightHomEntry x X q j =
              AtomHom.zero x.D _ _ := by
            unfold Unitor.rightHomEntry
            simp only [dif_neg (Ne.symm hj)]
          rw [hz, AtomHom.zero_comp
            realComputableShiftedRawDCT.laws.D]
          simp only [hj, if_false]

/-! ## Normalization of the shifted connector on the double-unit face -/

/-- The saved scalar-rescaling table is one on the eight entries
`(a,0,0)`.  This is a unit-face lookup, not a fourfold connector
calculation. -/
private theorem realLeanBetaTable_right_unit_unit (a : ZMod 8) :
    GaugeChi.realLeanBetaTable
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd 0)
        (Multiplicative.ofAdd 0) = 1 := by
  exact RealUnitFaceTable.beta_right_unit a 0

/-- Consequently the actual computable shift does not rescale
`T(a,0,0)`. -/
private theorem realComputableShiftBeta_right_unit_unit (a : ZMod 8) :
    shiftBeta realComputableNuBeta.data a 0 0 = 1 := by
  unfold shiftBeta
  rw [realComputableNuBeta_beta_eq_realLeanBetaTable]
  rw [realLeanBetaTable_right_unit_unit, dyadicRealHom_one]

/-- The executable parity cochain itself is normalized on the right unit;
this spelling avoids unfolding the surrounding `ShiftData` record. -/
private theorem realComputableNuBetaShiftNu_right_unit (a : ZMod 8) :
    shiftNu realComputableNuBeta.data a 0 = 0 := by
  change realComputableNuBeta.data.nu
      (Multiplicative.ofAdd a) (Multiplicative.ofAdd 0) = 0
  exact (realComputableNuBeta.laws.nu_normalized
    (Multiplicative.ofAdd a)).2

/-- The left coordinate comparison has no sign on `(a,0,0)`. -/
private theorem leftRouteFrameSign_right_unit_unit (a : ZMod 8)
    (r : realCData.Index a 0) :
    leftRouteFrameSign realCData realComputableNuBeta.data a 0 0 r = 1 := by
  unfold leftRouteFrameSign
  rw [add_zero, realComputableNuBetaShiftNu_right_unit, zero_mul,
    shiftParitySign_zero]

/-- The right coordinate comparison has no sign on `(a,0,0)`. -/
private theorem rightRouteFrameSign_right_unit_unit (a : ZMod 8)
    (r : realCData.Index 0 0) :
    rightRouteFrameSign realCData realComputableNuBeta.data a 0 0 r = 1 := by
  unfold rightRouteFrameSign
  rw [zero_add, realComputableNuBetaShiftNu_right_unit, zero_mul,
    shiftParitySign_zero]

/-- The frozen forward connector is the identity coefficient on its
double-right-unit face.  Only the eight stored `forwardCoeff (a,0,0)` rows
are reduced here. -/
private theorem realRawHomCoefficient_right_unit_unit (a : ZMod 8)
    (ab : realCData.Index a 0)
    (abc : realCData.Index (a + 0) 0)
    (bc : realCData.Index 0 0)
    (a_bc : realCData.Index a (0 + 0)) :
    Associator.homCoefficient realRawDCT.data a 0 0 ab abc bc a_bc =
      (realRawDCT.data.D.algebra (a + 0 + 0)).one := by
  change FusionTable.Index a 0 at ab
  change FusionTable.Index (a + 0) 0 at abc
  change FusionTable.Index 0 0 at bc
  change FusionTable.Index a (0 + 0) at a_bc
  unfold Associator.homCoefficient
  change CData.rawFinSum (realDData.algebra (a + 0 + 0)) (fun sourceAB =>
      CData.rawFinSum (realDData.algebra (a + 0 + 0)) (fun sourceABC =>
        (realDData.algebra (a + 0 + 0)).mul
          (realTForwardEntry a 0 0 bc a_bc sourceAB sourceABC)
          (Associator.leftDelta realRawDCT.data a 0 0
            ab abc sourceAB sourceABC))) = _
  have habuniq : ∀ r : realCData.Index a 0, r = ab := fun r =>
    (realUnitRowsLaws.right_unique a r).trans
      (realUnitRowsLaws.right_unique a ab).symm
  have habcuniq : ∀ r : realCData.Index (a + 0) 0, r = abc := fun r =>
    (realUnitRowsLaws.right_unique (a + 0) r).trans
      (realUnitRowsLaws.right_unique (a + 0) abc).symm
  rw [rawFinSum_eq_single_of_unique _
      (realDLaws.algebra_laws _) ab habuniq]
  rw [rawFinSum_eq_single_of_unique _
      (realDLaws.algebra_laws _) abc habcuniq]
  rw [Associator.leftDelta_source]
  change Coeff.mul (a + 0 + 0)
      (realTForwardEntry a 0 0 bc a_bc ab abc)
      (Coeff.one (a + 0 + 0)) = Coeff.one (a + 0 + 0)
  rw [Coeff.mul_one]
  rw [realUnitRowsLaws.left_unique 0 bc,
    realUnitRowsLaws.right_unique a a_bc,
    realUnitRowsLaws.right_unique a ab,
    realUnitRowsLaws.right_unique (a + 0) abc]
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ a = (n : ZMod 8) :=
    ⟨a.val, ZMod.val_lt a, (ZMod.natCast_zmod_val a).symm⟩
  interval_cases n <;> funext e <;> fin_cases e <;>
    simp [realTForwardEntry, realTLeftPosition, realTRightPosition,
      realUnitRowsData, Coeff.one] <;> rfl

/-- On this normalized face the inverse comparison sends a shifted delta
back to the identical raw delta. -/
private theorem leftRouteFrameInv_leftDelta_right_unit_unit (a : ZMod 8)
    (ab : x.C.Index a 0) (abc : x.C.Index (a + 0) 0) :
    leftRouteFrameInv realDData realCData realComputableNuBeta.data a 0 0
        (Associator.leftDelta x a 0 0 ab abc) =
      Associator.leftDelta realRawDCT.data a 0 0 ab abc := by
  funext r s
  unfold leftRouteFrameInv
  rw [leftRouteFrameSign_right_unit_unit,
    (realDLaws.algebra_laws _).one_smul]
  rfl

/-- The computably shifted associator retains the identity coefficient on
`(a,0,0)`. -/
private theorem realComputableShifted_homCoefficient_right_unit_unit
    (a : ZMod 8) (ab : x.C.Index a 0)
    (abc : x.C.Index (a + 0) 0) (bc : x.C.Index 0 0)
    (a_bc : x.C.Index a (0 + 0)) :
    Associator.homCoefficient x a 0 0 ab abc bc a_bc =
      (x.D.algebra (a + 0 + 0)).one := by
  change FusionTable.Index a 0 at ab
  change FusionTable.Index (a + 0) 0 at abc
  change FusionTable.Index 0 0 at bc
  change FusionTable.Index a (0 + 0) at a_bc
  unfold Associator.homCoefficient
  change rightRouteFrame realDData realCData realComputableNuBeta.data a 0 0
      (realTData.rightToCoord a 0 0
        (realTData.rightRoute.smul a 0 0
          (↑(shiftBeta realComputableNuBeta.data a 0 0)⁻¹ : ℝ)
          (realTData.hom a 0 0
            (realTData.leftOfCoord a 0 0
              (leftRouteFrameInv realDData realCData
                realComputableNuBeta.data a 0 0
                (Associator.leftDelta x a 0 0 ab abc)))))) bc a_bc = _
  rw [leftRouteFrameInv_leftDelta_right_unit_unit]
  rw [realT_right_toCoord_smul]
  unfold rightRouteFrame
  rw [rightRouteFrameSign_right_unit_unit]
  rw [realComputableShiftBeta_right_unit_unit]
  simp only [Units.val_one, inv_one]
  rw [(realDLaws.algebra_laws _).one_smul,
    (realDLaws.algebra_laws _).one_smul]
  exact realRawHomCoefficient_right_unit_unit a ab abc bc a_bc

/-! ## Endpoint normalization on the middle-unit face -/

/-- The endpoint correction of the concrete associator is trivial when its
middle object is the tensor unit.  The inner `X ⊗ 𝟙` fusion row is the
unique right-unit row, whose stored parity is zero. -/
theorem realAssociator_endpointSign_middle_unit (X Y : Obj)
    (qL : Tensor.Slot x.D x.C
      (Tensor.obj x.D x.C X Unitor.unit) Y) :
    RealAssociator.endpointSign X Unitor.unit Y qL = 1 := by
  unfold RealAssociator.endpointSign RealAssociator.leftInnerParity
  let xy := (Tensor.slots x.D x.C X Unitor.unit).get qL.left
  change paritySign
    (x.C.rowParity (X.atom xy.left).label 0 xy.fusion *
      (Y.atom qL.right).shift) = 1
  rw [realUnitRowsLaws.right_unique (X.atom xy.left).label xy.fusion]
  rw [realUnitRowsLaws.right_even, zero_mul, shiftParitySign_zero]

/-! ## Computable normalization of the whole middle-unit face -/

private abbrev rawX : RawDCTData := realRawDCT.data

/-- The saved scalar cochain is independent of its first argument on the
middle-unit face.  This is the only two-variable scalar-table reduction used
by the triangle proof. -/
private theorem realLeanBetaTable_middle_unit (a c : ZMod 8) :
    GaugeChi.realLeanBetaTable
        (Multiplicative.ofAdd a) (Multiplicative.ofAdd 0)
        (Multiplicative.ofAdd c) =
      GaugeChi.realLeanBetaTable
        (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 0)
        (Multiplicative.ofAdd c) := by
  exact RealUnitFaceTable.beta_middle_unit a c

/-- The actual computable `beta` used by the shifted connector has the same
middle-unit normalization as its saved dyadic table. -/
private theorem realComputableShiftBeta_middle_unit (a c : ZMod 8) :
    shiftBeta realComputableNuBeta.data a 0 c =
      shiftBeta realComputableNuBeta.data 0 0 c := by
  unfold shiftBeta
  rw [realComputableNuBeta_beta_eq_realLeanBetaTable,
    realComputableNuBeta_beta_eq_realLeanBetaTable,
    realLeanBetaTable_middle_unit]

/-- The raw row on a right-unit binary face is even.  This statement is
about the unshifted table used in the diagonal connector frames. -/
private theorem realRawRightUnitRowParity_zero (a : ZMod 8)
    (r : realCData.Index a 0) : realCData.rowParity a 0 r = 0 := by
  change FusionTable.indexParity a 0 r = 0
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ a = (n : ZMod 8) :=
    ⟨a.val, ZMod.val_lt a, (ZMod.natCast_zmod_val a).symm⟩
  interval_cases n <;> fin_cases r <;> rfl

/-- The raw row on a left-unit binary face is even. -/
private theorem realRawLeftUnitRowParity_zero (c : ZMod 8)
    (r : realCData.Index 0 c) : realCData.rowParity 0 c r = 0 := by
  change FusionTable.indexParity 0 c r = 0
  obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, n < 8 ∧ c = (n : ZMod 8) :=
    ⟨c.val, ZMod.val_lt c, (ZMod.natCast_zmod_val c).symm⟩
  interval_cases n <;> fin_cases r <;> rfl

/-- No source-frame sign is present on `T(a,0,c)`. -/
private theorem leftRouteFrameSign_middle_unit (a c : ZMod 8)
    (r : realCData.Index a 0) :
    leftRouteFrameSign realCData realComputableNuBeta.data a 0 c r = 1 := by
  unfold leftRouteFrameSign
  rw [realRawRightUnitRowParity_zero, mul_zero, shiftParitySign_zero]

/-- No target-frame sign is present on `T(a,0,c)`. -/
private theorem rightRouteFrameSign_middle_unit (a c : ZMod 8)
    (r : realCData.Index 0 c) :
    rightRouteFrameSign realCData realComputableNuBeta.data a 0 c r = 1 := by
  unfold rightRouteFrameSign
  rw [realRawLeftUnitRowParity_zero, mul_zero, shiftParitySign_zero]

/-- Extracting a raw connector coefficient through the abstract
`Associator.homCoefficient` interface returns the actual frozen table entry.
The proof collapses only the two delta-coordinate sums. -/
private theorem realRawHomCoefficient_eq_forwardEntry
    (a b c : ZMod 8)
    (sourceAB : rawX.C.Index a b)
    (sourceABC : rawX.C.Index (a + b) c)
    (targetBC : rawX.C.Index b c)
    (targetABC : rawX.C.Index a (b + c)) :
    Associator.homCoefficient rawX a b c
        sourceAB sourceABC targetBC targetABC =
      realTForwardEntry a b c targetBC targetABC sourceAB sourceABC := by
  change FusionTable.Index a b at sourceAB
  change FusionTable.Index (a + b) c at sourceABC
  change FusionTable.Index b c at targetBC
  change FusionTable.Index a (b + c) at targetABC
  unfold Associator.homCoefficient rawX
  change realTHom a b c
      (Associator.leftDelta rawX a b c sourceAB sourceABC)
        targetBC targetABC = _
  unfold realTHom CData.rawFinSum
  change (List.ofFn (fun sourceAB' =>
      (List.ofFn (fun sourceABC' =>
        Coeff.mul (a + b + c)
          (realTForwardEntry a b c targetBC targetABC
            sourceAB' sourceABC')
          (Associator.leftDelta rawX a b c sourceAB sourceABC
            sourceAB' sourceABC'))).sum)).sum = _
  rw [List.sum_ofFn]
  simp_rw [List.sum_ofFn]
  rw [Fintype.sum_eq_single sourceAB]
  · rw [Fintype.sum_eq_single sourceABC]
    · rw [Associator.leftDelta_source]
      exact Coeff.mul_one _ _
    · intro other hne
      rw [Associator.leftDelta_off_second rawX a b c
        sourceAB sourceABC other hne]
      exact Coeff.mul_zero _ _
  · intro other hne
    apply Finset.sum_eq_zero
    intro sourceABC' _
    rw [Associator.leftDelta_off_first rawX a b c
      sourceAB other sourceABC sourceABC' hne]
    exact Coeff.mul_zero _ _

/-! ### Imported frozen connector certificate

The 64 raw entries on `T(a,0,c)` are checked independently in
`RealMiddleUnitConnectorCertificate.forwardEntry_middle_unit`.
-/
/-- On the middle-unit face, removing the shifted source frame sends the
actual shifted delta coordinate to the identical raw delta coordinate. -/
private theorem leftRouteFrameInv_leftDelta_middle_unit (a c : ZMod 8)
    (sourceAB : x.C.Index a 0)
    (sourceABC : x.C.Index (a + 0) c) :
    leftRouteFrameInv realDData realCData realComputableNuBeta.data a 0 c
        (Associator.leftDelta x a 0 c sourceAB sourceABC) =
      Associator.leftDelta rawX a 0 c sourceAB sourceABC := by
  funext targetAB targetABC
  unfold leftRouteFrameInv
  rw [leftRouteFrameSign_middle_unit,
    (realDLaws.algebra_laws _).one_smul]
  rfl

/-- The actual computably shifted connector on `T(a,0,c)` is the transported
identity matrix multiplied by the actual stored `beta⁻¹`.  Both zero and
nonzero entries are statements about `realComputableShiftedRawDCT.data.T`,
not about an auxiliary table-only associator. -/
private theorem realComputableShifted_homCoefficient_middle_unit
    (a c : ZMod 8)
    (sourceAB : x.C.Index a 0)
    (sourceABC : x.C.Index (a + 0) c)
    (targetBC : x.C.Index 0 c)
    (targetABC : x.C.Index a (0 + c)) :
    Associator.homCoefficient x a 0 c
        sourceAB sourceABC targetBC targetABC =
      if Associator.castIndex rawX (add_zero a) rfl sourceABC =
          Associator.castIndex rawX rfl (zero_add c) targetABC then
        (x.D.algebra (a + 0 + c)).smul
          (↑(shiftBeta realComputableNuBeta.data 0 0 c)⁻¹ : ℝ)
          (x.D.algebra (a + 0 + c)).one
      else (x.D.algebra (a + 0 + c)).zero := by
  change FusionTable.Index a 0 at sourceAB
  change FusionTable.Index (a + 0) c at sourceABC
  change FusionTable.Index 0 c at targetBC
  change FusionTable.Index a (0 + c) at targetABC
  unfold Associator.homCoefficient
  change rightRouteFrame realDData realCData realComputableNuBeta.data a 0 c
      (realTData.rightToCoord a 0 c
        (realTData.rightRoute.smul a 0 c
          (↑(shiftBeta realComputableNuBeta.data a 0 c)⁻¹ : ℝ)
          (realTData.hom a 0 c
            (realTData.leftOfCoord a 0 c
              (leftRouteFrameInv realDData realCData
                realComputableNuBeta.data a 0 c
                (Associator.leftDelta x a 0 c
                  sourceAB sourceABC)))))) targetBC targetABC = _
  rw [leftRouteFrameInv_leftDelta_middle_unit]
  rw [realT_right_toCoord_smul]
  unfold rightRouteFrame
  rw [rightRouteFrameSign_middle_unit]
  rw [realComputableShiftBeta_middle_unit]
  rw [(realDLaws.algebra_laws _).one_smul]
  show (realDData.algebra (a + 0 + c)).smul
      (↑(shiftBeta realComputableNuBeta.data 0 0 c)⁻¹ : ℝ)
      (Associator.homCoefficient rawX a 0 c sourceAB sourceABC
        targetBC targetABC) = _
  rw [realRawHomCoefficient_eq_forwardEntry,
    RealMiddleUnitConnectorCertificate.forwardEntry_middle_unit]
  by_cases h : Associator.castIndex rawX (add_zero a) rfl sourceABC =
      Associator.castIndex rawX rfl (zero_add c) targetABC
  · simp only [if_pos h]
    rfl
  · simp only [if_neg h]
    show (realDData.algebra (a + 0 + c)).smul
        (↑(shiftBeta realComputableNuBeta.data 0 0 c)⁻¹ : ℝ)
        (realDData.algebra (a + 0 + c)).zero =
      (x.D.algebra (a + 0 + c)).zero
    rw [(realDLaws.algebra_laws _).smul_zero]
    rfl

/-! ### The actual left-unitor scalar -/

private theorem cast_algebra_smul_of_label_eq_middle_unit
    (dD : DData) {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier)
    (q : ℝ) (u : (dD.algebra a).carrier) :
    cast h ((dD.algebra a).smul q u) =
      (dD.algebra b).smul q (cast h u) := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

private theorem cast_algebra_zero_of_label_eq_middle_unit
    (dD : DData) {a b : ZMod 8} (hab : a = b)
    (h : (dD.algebra a).carrier = (dD.algebra b).carrier) :
    cast h (dD.algebra a).zero = (dD.algebra b).zero := by
  subst b
  have hh : h = rfl := Subsingleton.elim _ _
  cases hh
  rfl

/-- The inverse left-unitor coefficient is the actual middle-unit
connector scalar `beta⁻¹`, embedded as a multiple of the algebra unit. -/
private theorem realLeftInvCoefficient_eq_betaInv_smul_one
    (c : ZMod 8) (r : x.C.Index 0 c) :
    Unitor.leftInvCoefficient x realUnitRowsData c r =
      (x.D.algebra c).smul
        (↑(shiftBeta realComputableNuBeta.data 0 0 c)⁻¹ : ℝ)
        (x.D.algebra c).one := by
  let sourceABC := Associator.castIndex x (zero_add 0).symm rfl r
  let targetABC := Associator.castIndex x rfl (zero_add c).symm r
  have hmatch :
      Associator.castIndex rawX (add_zero 0) rfl sourceABC =
        Associator.castIndex rawX rfl (zero_add c) targetABC := by
    apply Fin.ext
    rfl
  unfold Unitor.leftInvCoefficient
  rw [realComputableShifted_homCoefficient_middle_unit]
  rw [if_pos hmatch]
  unfold Unitor.castUnitTriple
  rw [cast_algebra_smul_of_label_eq_middle_unit x.D
    (by simp only [zero_add])]
  rw [cast_algebra_one_of_label_eq x.D (by simp only [zero_add])]

/-- In any stored coefficient algebra, a left inverse of
`q⁻¹ • 1` must be `q • 1`. -/
private theorem eq_smul_one_of_inv_smul_one_mul_eq_one
    (d : SuperAlgebraData ℝ) (hd : SuperAlgebraLaws d)
    (q : ℝˣ) (u : d.carrier)
    (hu : d.mul (d.smul (↑q⁻¹ : ℝ) d.one) u = d.one) :
    u = d.smul (↑q : ℝ) d.one := by
  calc
    u = d.smul 1 u := (hd.one_smul u).symm
    _ = d.smul ((↑q : ℝ) * (↑q⁻¹ : ℝ)) u := by simp
    _ = d.smul (↑q : ℝ) (d.smul (↑q⁻¹ : ℝ) u) :=
      hd.smul_assoc _ _ _
    _ = d.smul (↑q : ℝ)
        (d.mul (d.smul (↑q⁻¹ : ℝ) d.one) u) := by
      rw [hd.smul_mul, hd.one_mul]
    _ = d.smul (↑q : ℝ) d.one := by rw [hu]

/-- The forward left-unitor coefficient is therefore the matching actual
`beta` scalar.  This conclusion uses the already proved two-sided connector
inverse law, rather than evaluating the inverse connector table again. -/
private theorem realLeftHomCoefficient_eq_beta_smul_one
    (c : ZMod 8) (r : x.C.Index 0 c) :
    Unitor.leftHomCoefficient x realUnitRowsData c r =
      (x.D.algebra c).smul
        (↑(shiftBeta realComputableNuBeta.data 0 0 c) : ℝ)
        (x.D.algebra c).one := by
  apply eq_smul_one_of_inv_smul_one_mul_eq_one
    (x.D.algebra c) (realComputableShiftedRawDCT.laws.D.algebra_laws c)
    (shiftBeta realComputableNuBeta.data 0 0 c)
  rw [← realLeftInvCoefficient_eq_betaInv_smul_one]
  exact leftCoefficient_hom_inv c r

/-! ### Coefficient convolution on one middle-unit route -/

/-- One summand of the triangle convolution is a Kronecker delta in the
two transported outer rows.  The two actual `beta` scalars cancel inside
the endpoint algebra. -/
private theorem middleUnitConvolutionTerm
    (a c : ZMod 8) (s t : ZMod 2)
    (sourceAB : x.C.Index a 0)
    (sourceABC : x.C.Index (a + 0) c)
    (targetBC : x.C.Index 0 c)
    (middleABC : x.C.Index a (0 + c))
    (targetAC : x.C.Index a c) :
    let sourceAC := Associator.castIndex x (add_zero a) rfl sourceABC
    let middleAC := Associator.castIndex x rfl (zero_add c) middleABC
    let hTotal : a + 0 + c = a + c := by simp only [add_zero]
    (x.D.algebra (a + c)).mul
        (Tensor.coefficient x.D x.C a c s t t middleAC targetAC
          (x.D.algebra a).one
          (Unitor.leftHomCoefficient x realUnitRowsData c targetBC))
        (cast
          (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hTotal)
          (Associator.homCoefficient x a 0 c sourceAB sourceABC
            targetBC middleABC)) =
      if targetAC = middleAC ∧ sourceAC = middleAC then
        (x.D.algebra (a + c)).one
      else (x.D.algebra (a + c)).zero := by
  dsimp only
  let q := shiftBeta realComputableNuBeta.data 0 0 c
  let sourceAC := Associator.castIndex x (add_zero a) rfl sourceABC
  let middleAC := Associator.castIndex x rfl (zero_add c) middleABC
  let rawSourceAC := Associator.castIndex rawX (add_zero a) rfl sourceABC
  let rawMiddleAC := Associator.castIndex rawX rfl (zero_add c) middleABC
  have hShiftToRaw : sourceAC = middleAC → rawSourceAC = rawMiddleAC := by
    intro h
    apply Fin.ext
    simpa only [sourceAC, middleAC, rawSourceAC, rawMiddleAC,
      castIndex_val] using congrArg Fin.val h
  have hRawToShift : rawSourceAC = rawMiddleAC → sourceAC = middleAC := by
    intro h
    apply Fin.ext
    simpa only [sourceAC, middleAC, rawSourceAC, rawMiddleAC,
      castIndex_val] using congrArg Fin.val h
  rw [realLeftHomCoefficient_eq_beta_smul_one]
  rw [Tensor.coefficient_smul_right x.D
    realComputableShiftedRawDCT.laws.D x.C
    realComputableShiftedRawDCT.laws.C]
  rw [Tensor.coefficient_one x.D
    realComputableShiftedRawDCT.laws.D x.C
    realComputableShiftedRawDCT.laws.C]
  rw [realComputableShifted_homCoefficient_middle_unit]
  change (x.D.algebra (a + c)).mul
      ((x.D.algebra (a + c)).smul (↑q : ℝ)
        (if targetAC = middleAC then (x.D.algebra (a + c)).one
          else (x.D.algebra (a + c)).zero))
      (cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier)
          (by simp only [add_zero] : a + 0 + c = a + c))
        (if rawSourceAC = rawMiddleAC then
          (x.D.algebra (a + 0 + c)).smul (↑q⁻¹ : ℝ)
            (x.D.algebra (a + 0 + c)).one
        else (x.D.algebra (a + 0 + c)).zero)) = _
  by_cases hTarget : targetAC = middleAC
  · by_cases hSource : sourceAC = middleAC
    · have hRaw := hShiftToRaw hSource
      rw [if_pos hTarget, if_pos hRaw, if_pos ⟨hTarget, hSource⟩]
      rw [cast_algebra_smul_of_label_eq_middle_unit x.D
        (by simp only [add_zero] : a + 0 + c = a + c)]
      rw [cast_algebra_one_of_label_eq x.D
        (by simp only [add_zero] : a + 0 + c = a + c)]
      rw [(realComputableShiftedRawDCT.laws.D.algebra_laws _).smul_mul]
      rw [(realComputableShiftedRawDCT.laws.D.algebra_laws _).one_mul]
      rw [← (realComputableShiftedRawDCT.laws.D.algebra_laws _).smul_assoc]
      have hq : (↑q : ℝ) * (↑q⁻¹ : ℝ) = 1 := by simp
      rw [hq, (realComputableShiftedRawDCT.laws.D.algebra_laws _).one_smul]
    · have hRaw : rawSourceAC ≠ rawMiddleAC := by
        intro h
        exact hSource (hRawToShift h)
      rw [if_pos hTarget, if_neg hRaw]
      rw [cast_algebra_zero_of_label_eq_middle_unit x.D
        (by simp only [add_zero] : a + 0 + c = a + c)]
      rw [show ∀ (u : (x.D.algebra (a + c)).carrier),
          (x.D.algebra (a + c)).mul u (x.D.algebra (a + c)).zero =
            (x.D.algebra (a + c)).zero from fun u => by
        have h := (realComputableShiftedRawDCT.laws.D.algebra_laws
          (a + c)).mul_smul 0 u (x.D.algebra (a + c)).zero
        rw [(realComputableShiftedRawDCT.laws.D.algebra_laws
          (a + c)).zero_smul,
          (realComputableShiftedRawDCT.laws.D.algebra_laws
            (a + c)).zero_smul] at h
        exact h]
      rw [if_neg (fun hcon => hSource hcon.2)]
  · rw [if_neg hTarget]
    rw [(realComputableShiftedRawDCT.laws.D.algebra_laws _).smul_zero]
    rw [show ∀ (u : (x.D.algebra (a + c)).carrier),
        (x.D.algebra (a + c)).mul
            (realComputableShiftedRawDCT.data.D.algebra (a + c)).zero u =
          (x.D.algebra (a + c)).zero from fun u => by
      have h2 := (realComputableShiftedRawDCT.laws.D.algebra_laws
        (a + c)).smul_mul 0
        ((realComputableShiftedRawDCT.data.D.algebra (a + c)).zero) u
      rw [(realComputableShiftedRawDCT.laws.D.algebra_laws
        (a + c)).zero_smul,
        (realComputableShiftedRawDCT.laws.D.algebra_laws
          (a + c)).zero_smul] at h2
      exact h2]
    rw [if_neg (fun hcon => hTarget hcon.1)]

/-- A fixed-order raw algebra sum with only one possible nonzero index
reduces to that index. -/
private theorem rawFinSum_eq_single
    (d : SuperAlgebraData ℝ) (hd : SuperAlgebraLaws d)
    {n : ℕ} (k : Fin n) (f : Fin n → d.carrier)
    (hzero : ∀ i, i ≠ k → f i = d.zero) :
    CData.rawFinSum d f = f k := by
  letI : Zero d.carrier := ⟨d.zero⟩
  letI : Add d.carrier := ⟨d.add⟩
  letI : Neg d.carrier := ⟨d.neg⟩
  letI : Sub d.carrier := ⟨fun u v => d.add u (d.neg v)⟩
  letI : AddCommGroup d.carrier :=
    { add_assoc := hd.add_assoc
      zero_add := hd.zero_add
      add_zero := hd.add_zero
      neg_add_cancel := hd.neg_add
      add_comm := hd.add_comm
      sub_eq_add_neg := fun _ _ => rfl
      nsmul := nsmulRec
      zsmul := zsmulRec }
  unfold CData.rawFinSum
  change (List.ofFn f).sum = f k
  rw [List.sum_ofFn]
  exact Finset.sum_eq_single k
    (fun i _ hik => hzero i hik)
    (fun hk => (hk (Finset.mem_univ k)).elim)

/-- Summing over the intermediate right-route outer row gives exactly the
binary tensor identity coefficient.  This is the complete numerical content
needed from the middle-unit face; it involves threefold connectors only. -/
private theorem middleUnitCoefficientConvolution
    (a c : ZMod 8) (s t : ZMod 2)
    (sourceAB : x.C.Index a 0)
    (sourceABC : x.C.Index (a + 0) c)
    (targetBC : x.C.Index 0 c)
    (targetAC : x.C.Index a c) :
    let sourceAC := Associator.castIndex x (add_zero a) rfl sourceABC
    let hTotal : a + 0 + c = a + c := by simp only [add_zero]
    CData.rawFinSum (x.D.algebra (a + c)) (fun middleABC =>
      (x.D.algebra (a + c)).mul
        (Tensor.coefficient x.D x.C a c s t t
          (Associator.castIndex x rfl (zero_add c) middleABC) targetAC
          (x.D.algebra a).one
          (Unitor.leftHomCoefficient x realUnitRowsData c targetBC))
        (cast
          (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hTotal)
          (Associator.homCoefficient x a 0 c sourceAB sourceABC
            targetBC middleABC))) =
      Tensor.coefficient x.D x.C a c s t t sourceAC targetAC
        (x.D.algebra a).one (x.D.algebra c).one := by
  dsimp only
  let sourceAC := Associator.castIndex x (add_zero a) rfl sourceABC
  let middleABC₀ := Associator.castIndex x rfl (zero_add c).symm sourceAC
  have hmiddle₀ :
      Associator.castIndex x rfl (zero_add c) middleABC₀ = sourceAC := by
    apply Fin.ext
    simp only [middleABC₀, castIndex_val]
  rw [Tensor.coefficient_one x.D
    realComputableShiftedRawDCT.laws.D x.C
    realComputableShiftedRawDCT.laws.C]
  by_cases hTarget : targetAC = sourceAC
  · rw [if_pos hTarget]
    rw [rawFinSum_eq_single (x.D.algebra (a + c))
      (realComputableShiftedRawDCT.laws.D.algebra_laws (a + c))
      middleABC₀]
    · rw [middleUnitConvolutionTerm]
      simp only [hmiddle₀, hTarget, and_self, if_true]
      exact if_pos ⟨trivial, rfl⟩
    · intro middleABC hne
      rw [middleUnitConvolutionTerm]
      have hMiddle :
          Associator.castIndex x rfl (zero_add c) middleABC ≠ sourceAC := by
        intro h
        apply hne
        apply castIndex_injective x rfl (zero_add c)
        rw [h, hmiddle₀]
      have hTargetMiddle :
          targetAC ≠ Associator.castIndex x rfl (zero_add c) middleABC := by
        simpa only [hTarget] using hMiddle.symm
      simp only [hTargetMiddle, false_and, if_false]
  · rw [if_neg hTarget]
    rw [rawFinSum_eq_single (x.D.algebra (a + c))
      (realComputableShiftedRawDCT.laws.D.algebra_laws (a + c))
      middleABC₀]
    · rw [middleUnitConvolutionTerm]
      simp only [hmiddle₀, hTarget, false_and, if_false]
    · intro middleABC _
      rw [middleUnitConvolutionTerm]
      by_cases hMiddle :
          Associator.castIndex x rfl (zero_add c) middleABC = sourceAC
      · have hTargetMiddle :
            targetAC ≠ Associator.castIndex x rfl (zero_add c) middleABC := by
          simpa only [hMiddle] using hTarget
        simp only [hTargetMiddle, false_and, if_false]
      · have hSourceMiddle :
            sourceAC ≠ Associator.castIndex x rfl (zero_add c) middleABC :=
          Ne.symm hMiddle
        rw [if_neg (fun hcon => hSourceMiddle hcon.2)]

/-! ## Label transport for the binary tensor coefficient -/

/-- Transporting the right input label transports the two fusion rows, the
right coefficient, and the output coefficient in the evident way. -/
private theorem tensorCoefficient_cast_right_label
    (a b b' : ZMod 8) (h : b = b') (s t t' : ZMod 2)
    (source target : x.C.Index a b)
    (u : (x.D.algebra a).carrier) (v : (x.D.algebra b).carrier) :
    cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier)
          (congrArg (fun z : ZMod 8 => a + z) h))
        (Tensor.coefficient x.D x.C a b s t t' source target u v) =
      Tensor.coefficient x.D x.C a b' s t t'
        (Associator.castIndex x rfl h source)
        (Associator.castIndex x rfl h target) u
        (cast (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) h) v) := by
  cases h
  rfl

/-- The analogous transport law for the left input label. -/
private theorem tensorCoefficient_cast_left_label
    (a a' b : ZMod 8) (h : a = a') (s t t' : ZMod 2)
    (source target : x.C.Index a b)
    (u : (x.D.algebra a).carrier) (v : (x.D.algebra b).carrier) :
    cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier)
          (congrArg (fun z : ZMod 8 => z + b) h))
        (Tensor.coefficient x.D x.C a b s t t' source target u v) =
      Tensor.coefficient x.D x.C a' b s t t'
        (Associator.castIndex x h rfl source)
        (Associator.castIndex x h rfl target)
        (cast (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) h) u) v := by
  cases h
  rfl

/-! ### Tensor entries on the two middle-unit routes -/

/-- The right-associated middle-unit route and its binary endpoint carry
the same total label. -/
private theorem middleRightRoute_binaryLabelEq
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (middleABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label))
    (targetAC : x.C.Index (X.atom i).label (Y.atom j).label) :
    (Tensor.slotAtom x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y)
      (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
        i u j targetBC middleABC)).label =
      (Tensor.slotAtom x.D x.C X Y ⟨i, j, targetAC⟩).label := by
  rw [RealAssociatorLaws.rightRouteSlot_label]
  change (X.atom i).label + (0 + (Y.atom j).label) =
    (X.atom i).label + (Y.atom j).label
  rw [zero_add]

/-- The left-associated middle-unit route and its binary endpoint carry the
same total label. -/
private theorem middleLeftRoute_binaryLabelEq
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetAC : x.C.Index (X.atom i).label (Y.atom j).label) :
    (Tensor.slotAtom x.D x.C (Tensor.obj x.D x.C X Unitor.unit) Y
      (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
        i u j sourceAB sourceABC)).label =
      (Tensor.slotAtom x.D x.C X Y ⟨i, j, targetAC⟩).label := by
  rw [RealAssociatorLaws.leftRouteSlot_label]
  change (X.atom i).label + 0 + (Y.atom j).label =
    (X.atom i).label + (Y.atom j).label
  rw [add_zero]

/-- Once the two endpoint labels are fixed, a tensor block is literally the
stored binary coefficient.  This is the small route-transport lemma already
used by the associator-naturality proof, specialized here to the same shifted
real kernel. -/
private theorem realTensorEntry_coeff_of_label_eq
    {X X' Y Y' : Obj}
    (f : Hom x.D X X') (g : Hom x.D Y Y')
    (q : Tensor.Slot x.D x.C X Y)
    (q' : Tensor.Slot x.D x.C X' Y')
    (hA : (X.atom q.left).label = (X'.atom q'.left).label)
    (hB : (Y.atom q.right).label = (Y'.atom q'.right).label)
    (hQ : (Tensor.slotAtom x.D x.C X Y q).label =
      (Tensor.slotAtom x.D x.C X' Y' q').label) :
    (Tensor.entry x.D x.C f g q q').coeff hQ =
      Tensor.coefficient x.D x.C
        (X.atom q.left).label (Y.atom q.right).label
        (X.atom q.left).shift (Y.atom q.right).shift
        (Y'.atom q'.right).shift q.fusion
        (Associator.castIndex x hA.symm hB.symm q'.fusion)
        ((f q.left q'.left).coeff hA)
        ((g q.right q'.right).coeff hB) := by
  simp [Tensor.entry, hA, hB, Associator.castIndex]

private theorem cast_proof_irrel_middle_unit {A B : Type}
    (h h' : A = B) (u : A) : cast h u = cast h' u := by
  rw [Subsingleton.elim h h']

private theorem cast_function_injective_middle_unit {A B : Type}
    (h : A = B) : Function.Injective (cast h) := by
  cases h
  intro u v huv
  exact huv

private theorem castIndex_trans_middle_unit
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

private theorem castIndex_irrel_middle_unit
    {a b a' b' : ZMod 8} (ha ha' : a = a') (hb hb' : b = b')
    (r : x.C.Index a b) :
    Associator.castIndex x ha hb r = Associator.castIndex x ha' hb' r := by
  subst a'
  subst b'
  rfl

private theorem castIndex_self_middle_unit
    {a b : ZMod 8} (ha : a = a) (hb : b = b)
    (r : x.C.Index a b) :
    Associator.castIndex x ha hb r = r := by
  rw [castIndex_irrel_middle_unit ha rfl hb rfl]
  rfl

/-- After transporting the right-associated route to the binary endpoint,
its tensor block is the binary coefficient carrying the actual forward left
unitor scalar. -/
private theorem middleRightTensorEntry_coeff
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (middleABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label))
    (targetAC : x.C.Index (X.atom i).label (Y.atom j).label) :
    let qR := RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
      i u j targetBC middleABC
    let qAC : Tensor.Slot x.D x.C X Y := ⟨i, j, targetAC⟩
    let hRight := middleRightRoute_binaryLabelEq X Y i u j
      targetBC middleABC targetAC
    cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hRight)
        ((Tensor.entry x.D x.C (Hom.id x.D X)
          (Unitor.leftHom x realUnitRowsData Y) qR qAC).coeff hRight) =
      Tensor.coefficient x.D x.C
        (X.atom i).label (Y.atom j).label
        (X.atom i).shift (Y.atom j).shift (Y.atom j).shift
        (Associator.castIndex x rfl (zero_add (Y.atom j).label) middleABC)
        targetAC (x.D.algebra (X.atom i).label).one
        (Unitor.leftHomCoefficient x realUnitRowsData
          (Y.atom j).label targetBC) := by
  dsimp only
  let qR := RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
    i u j targetBC middleABC
  let qAC : Tensor.Slot x.D x.C X Y := ⟨i, j, targetAC⟩
  let hRight := middleRightRoute_binaryLabelEq X Y i u j
    targetBC middleABC targetAC
  have hInnerAtom :
      (Tensor.obj x.D x.C Unitor.unit Y).atom qR.right = Y.atom j := by
    change Tensor.slotAtom x.D x.C Unitor.unit Y
      ((Tensor.slots x.D x.C Unitor.unit Y).get qR.right) = Y.atom j
    rw [show (Tensor.slots x.D x.C Unitor.unit Y).get qR.right =
        ⟨u, j, targetBC⟩ by
      simpa only [qR] using
        (RealAssociatorLaws.rightRouteSlot_inner X Unitor.unit Y
          i u j targetBC middleABC)]
    exact leftSlotAtom_eq Y ⟨u, j, targetBC⟩
  let hA : (X.atom qR.left).label = (X.atom qAC.left).label := by
    show (X.atom (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
      i u j targetBC middleABC).left).label = (X.atom i).label
    rw [RealAssociatorLaws.rightRouteSlot_left]
  let hB : ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).label =
      (Y.atom qAC.right).label := by
    simpa only [qAC, Tensor.Slot.right] using congrArg Atom.label hInnerAtom
  have hEntry := realTensorEntry_coeff_of_label_eq
    (Hom.id x.D X) (Unitor.leftHom x realUnitRowsData Y)
    qR qAC hA hB hRight
  have hEntryCast := congrArg
    (cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hRight))
    hEntry
  have hProof :
      congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hRight =
        congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier)
          (congrArg (fun w : ZMod 8 => (X.atom qR.left).label + w) hB) :=
    Subsingleton.elim _ _
  rw [hProof] at hEntryCast
  have htest := tensorCoefficient_cast_right_label
    (X.atom qR.left).label
    ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).label
    (Y.atom qAC.right).label hB
    (X.atom qR.left).shift
    ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).shift
    (Y.atom qAC.right).shift
    qR.fusion (Associator.castIndex x hA.symm hB.symm qAC.fusion)
    ((Hom.id x.D X qR.left qAC.left).coeff hA)
    ((Unitor.leftHom x realUnitRowsData Y qR.right qAC.right).coeff hB)
  have hswap :
      cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hRight)
        (Tensor.coefficient x.D x.C (X.atom qR.left).label
          ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).label
          (X.atom qR.left).shift
          ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).shift
          (Y.atom qAC.right).shift qR.fusion
          (Associator.castIndex x hA.symm hB.symm qAC.fusion)
          ((Hom.id x.D X qR.left qAC.left).coeff hA)
          ((Unitor.leftHom x realUnitRowsData Y qR.right
            qAC.right).coeff hB)) =
      cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier)
          (congrArg (fun w : ZMod 8 => (X.atom qR.left).label + w) hB))
        (Tensor.coefficient x.D x.C (X.atom qR.left).label
          ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).label
          (X.atom qR.left).shift
          ((Tensor.obj x.D x.C Unitor.unit Y).atom qR.right).shift
          (Y.atom qAC.right).shift qR.fusion
          (Associator.castIndex x hA.symm hB.symm qAC.fusion)
          ((Hom.id x.D X qR.left qAC.left).coeff hA)
          ((Unitor.leftHom x realUnitRowsData Y qR.right
            qAC.right).coeff hB)) :=
    cast_proof_irrel_middle_unit _ _ _
  have hEntryCast2 := hEntryCast.trans (hswap.trans htest)
  have hSource :
      Associator.castIndex x rfl hB qR.fusion =
        Associator.castIndex x rfl (zero_add (Y.atom j).label) middleABC := by
    apply Fin.ext
    have hOuter := congrArg Fin.val
      (RealAssociatorLaws.rightRouteSlot_outerRow X Unitor.unit Y
        i u j targetBC middleABC)
    simpa only [qR, castIndex_val] using hOuter
  have hTarget :
      Associator.castIndex x rfl hB
          (Associator.castIndex x hA.symm hB.symm qAC.fusion) = targetAC := by
    apply Fin.ext
    simp only [qAC, Tensor.Slot.fusion, castIndex_val]
  have hId :
      ((Hom.id x.D X) qR.left qAC.left).coeff hA =
        (x.D.algebra (X.atom i).label).one := by
    simp [Hom.id, qR, qAC, hA, Tensor.Slot.left]
    rw [if_pos (show (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
      i u j targetBC middleABC).fst = i from rfl)]
    rw [Subsingleton.elim hA (rfl : (X.atom i).label = (X.atom i).label)]
    exact AtomHom.coeff_id (X.atom i)
  have hLeft :
      cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hB)
          (((Unitor.leftHom x realUnitRowsData Y) qR.right qAC.right).coeff hB) =
        Unitor.leftHomCoefficient x realUnitRowsData
          (Y.atom j).label targetBC := by
    have hgen : ∀ (sl : Tensor.Slot x.D x.C Unitor.unit Y)
        (_hsl : sl = ⟨u, j, targetBC⟩)
        (hB' : (Tensor.slotAtom x.D x.C Unitor.unit Y sl).label =
          (Y.atom j).label),
        cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hB')
            ((Unitor.leftHomEntry x realUnitRowsData Y sl j).coeff hB') =
          Unitor.leftHomCoefficient x realUnitRowsData
            (Y.atom j).label targetBC := by
      intro sl hsl hB'
      subst hsl
      rw [show Unitor.leftHomEntry x realUnitRowsData Y
          (⟨u, j, targetBC⟩ : Tensor.Slot x.D x.C Unitor.unit Y) j =
        AtomHom.ofLabelEq
          (show (Tensor.slotAtom x.D x.C Unitor.unit Y
              ⟨u, j, targetBC⟩).label = (Y.atom j).label from
            zero_add _)
          (cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
              (show (Tensor.slotAtom x.D x.C Unitor.unit Y
                  ⟨u, j, targetBC⟩).label = (Y.atom j).label from
                zero_add _)).symm
            (Unitor.leftHomCoefficient x realUnitRowsData
              (Y.atom j).label targetBC)) from by
        unfold Unitor.leftHomEntry
        rw [dif_pos (show Tensor.Slot.right
          (⟨u, j, targetBC⟩ : Tensor.Slot x.D x.C Unitor.unit Y) = j
          from rfl)]
        rfl]
      rw [Subsingleton.elim hB'
        (show (Tensor.slotAtom x.D x.C Unitor.unit Y
            ⟨u, j, targetBC⟩).label = (Y.atom j).label from zero_add _)]
      rw [AtomHom.coeff_ofLabelEq]
      simp
    exact hgen ((Tensor.slots x.D x.C Unitor.unit Y).get qR.right)
      (by simpa only [qR] using
        (RealAssociatorLaws.rightRouteSlot_inner X Unitor.unit Y
          i u j targetBC middleABC))
      hB
  convert hEntryCast2 using 2
  rw [hId, hLeft]
  rw [show qAC.fusion = targetAC from rfl]
  congr 1
  · rw [hInnerAtom]
  · rw [show qR.fusion = Associator.castIndex x
        (rfl : (X.atom qR.left).label = (X.atom qR.left).label)
        ((zero_add ((Y.atom j).label)).trans
          (congrArg Atom.label hInnerAtom).symm) middleABC from rfl]
    rw [castIndex_trans_middle_unit]
    exact castIndex_irrel_middle_unit _ _ _ _ _
  · rw [castIndex_trans_middle_unit]
    exact (castIndex_self_middle_unit _ _ _).symm

/-- The left-associated route transports to the same binary coefficient,
with the strict right-unitor coefficient and the identity on the second
factor. -/
private theorem middleLeftTensorEntry_coeff
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetAC : x.C.Index (X.atom i).label (Y.atom j).label) :
    let qL := RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
      i u j sourceAB sourceABC
    let qAC : Tensor.Slot x.D x.C X Y := ⟨i, j, targetAC⟩
    let hLeft := middleLeftRoute_binaryLabelEq X Y i u j
      sourceAB sourceABC targetAC
    cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hLeft)
        ((Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y)
          qL qAC).coeff hLeft) =
      Tensor.coefficient x.D x.C
        (X.atom i).label (Y.atom j).label
        (X.atom i).shift (Y.atom j).shift (Y.atom j).shift
        (Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC)
        targetAC (x.D.algebra (X.atom i).label).one
        (x.D.algebra (Y.atom j).label).one := by
  dsimp only
  let qL := RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
    i u j sourceAB sourceABC
  let qAC : Tensor.Slot x.D x.C X Y := ⟨i, j, targetAC⟩
  let hLeft := middleLeftRoute_binaryLabelEq X Y i u j
    sourceAB sourceABC targetAC
  have hInnerAtom :
      (Tensor.obj x.D x.C X Unitor.unit).atom qL.left = X.atom i := by
    change Tensor.slotAtom x.D x.C X Unitor.unit
      ((Tensor.slots x.D x.C X Unitor.unit).get qL.left) = X.atom i
    rw [show (Tensor.slots x.D x.C X Unitor.unit).get qL.left =
        ⟨i, u, sourceAB⟩ by
      simpa only [qL] using
        (RealAssociatorLaws.leftRouteSlot_inner X Unitor.unit Y
          i u j sourceAB sourceABC)]
    exact rightSlotAtom_eq X ⟨i, u, sourceAB⟩
  let hA : ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).label =
      (X.atom qAC.left).label := by
    simpa only [qAC, Tensor.Slot.left] using congrArg Atom.label hInnerAtom
  let hB : (Y.atom qL.right).label = (Y.atom qAC.right).label := rfl
  have hEntry := realTensorEntry_coeff_of_label_eq
    (Unitor.rightHom x X) (Hom.id x.D Y) qL qAC hA hB hLeft
  have hEntryCast := congrArg
    (cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hLeft))
    hEntry
  have hProof :
      congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hLeft =
        congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier)
          (congrArg (fun w : ZMod 8 => w + (Y.atom qL.right).label) hA) :=
    Subsingleton.elim _ _
  rw [hProof] at hEntryCast
  have htest := tensorCoefficient_cast_left_label
    ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).label
    (X.atom qAC.left).label
    (Y.atom qL.right).label hA
    ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).shift
    (Y.atom qL.right).shift
    (Y.atom qAC.right).shift
    qL.fusion (Associator.castIndex x hA.symm hB.symm qAC.fusion)
    (((Unitor.rightHom x X) qL.left qAC.left).coeff hA)
    (((Hom.id x.D Y) qL.right qAC.right).coeff hB)
  have hswap :
      cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hLeft)
        (Tensor.coefficient x.D x.C
          ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).label
          (Y.atom qL.right).label
          ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).shift
          (Y.atom qL.right).shift
          (Y.atom qAC.right).shift qL.fusion
          (Associator.castIndex x hA.symm hB.symm qAC.fusion)
          (((Unitor.rightHom x X) qL.left qAC.left).coeff hA)
          (((Hom.id x.D Y) qL.right qAC.right).coeff hB)) =
      cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier)
          (congrArg (fun w : ZMod 8 => w + (Y.atom qL.right).label) hA))
        (Tensor.coefficient x.D x.C
          ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).label
          (Y.atom qL.right).label
          ((Tensor.obj x.D x.C X Unitor.unit).atom qL.left).shift
          (Y.atom qL.right).shift
          (Y.atom qAC.right).shift qL.fusion
          (Associator.castIndex x hA.symm hB.symm qAC.fusion)
          (((Unitor.rightHom x X) qL.left qAC.left).coeff hA)
          (((Hom.id x.D Y) qL.right qAC.right).coeff hB)) :=
    cast_proof_irrel_middle_unit _ _ _
  have hEntryCast2 := hEntryCast.trans (hswap.trans htest)
  have hRightCoeff :
      cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hA)
          (((Unitor.rightHom x X) qL.left qAC.left).coeff hA) =
        (x.D.algebra (X.atom i).label).one := by
    have hgen : ∀ (sl : Tensor.Slot x.D x.C X Unitor.unit)
        (_hsl : sl = ⟨i, u, sourceAB⟩)
        (hA' : (Tensor.slotAtom x.D x.C X Unitor.unit sl).label =
          (X.atom i).label),
        cast (congrArg (fun w : ZMod 8 => (x.D.algebra w).carrier) hA')
            ((Unitor.rightHomEntry x X sl i).coeff hA') =
          (x.D.algebra (X.atom i).label).one := by
      intro sl hsl hA'
      subst hsl
      rw [show Unitor.rightHomEntry x X
          (⟨i, u, sourceAB⟩ : Tensor.Slot x.D x.C X Unitor.unit) i =
        AtomHom.ofLabelEq
          (show (Tensor.slotAtom x.D x.C X Unitor.unit
              ⟨i, u, sourceAB⟩).label = (X.atom i).label from
            add_zero _)
          (cast (congrArg (fun t : ZMod 8 => (x.D.algebra t).carrier)
              (show (Tensor.slotAtom x.D x.C X Unitor.unit
                  ⟨i, u, sourceAB⟩).label = (X.atom i).label from
                add_zero _)).symm
            (x.D.algebra (X.atom i).label).one) from by
        unfold Unitor.rightHomEntry
        rw [dif_pos (show Tensor.Slot.left
          (⟨i, u, sourceAB⟩ : Tensor.Slot x.D x.C X Unitor.unit) = i
          from rfl)]
        rfl]
      rw [Subsingleton.elim hA'
        (show (Tensor.slotAtom x.D x.C X Unitor.unit
            ⟨i, u, sourceAB⟩).label = (X.atom i).label from add_zero _)]
      rw [AtomHom.coeff_ofLabelEq]
      simp
    exact hgen ((Tensor.slots x.D x.C X Unitor.unit).get qL.left)
      (by simpa only [qL] using
        (RealAssociatorLaws.leftRouteSlot_inner X Unitor.unit Y
          i u j sourceAB sourceABC))
      hA
  have hId :
      ((Hom.id x.D Y) qL.right qAC.right).coeff hB =
        (x.D.algebra (Y.atom j).label).one := by
    simp [Hom.id, qL, qAC, hB]
    rw [if_pos (show j = Tensor.Slot.right
      (⟨i, j, targetAC⟩ : Tensor.Slot x.D x.C X Y) from rfl)]
    rw [Subsingleton.elim hB (rfl : (Y.atom j).label = (Y.atom j).label)]
    exact AtomHom.coeff_id (Y.atom j)
  convert hEntryCast2 using 2
  rw [hRightCoeff, hId]
  rw [show qAC.fusion = targetAC from rfl]
  congr 1
  · rw [hInnerAtom]
  · rw [show qL.fusion = Associator.castIndex x
        ((add_zero ((X.atom i).label)).trans
          (congrArg Atom.label hInnerAtom).symm)
        (rfl : (Y.atom qL.right).label = (Y.atom qL.right).label)
        sourceABC from rfl]
    rw [castIndex_trans_middle_unit]
    exact castIndex_irrel_middle_unit _ _ _ _ _
  · rw [castIndex_trans_middle_unit]
    exact (castIndex_self_middle_unit _ _ _).symm

/-! ## Middle-unit associator entries -/

private theorem realAssociatorHomEntry_zero_of_left_ne (X Y : Obj)
    (qL : Tensor.Slot x.D x.C (Tensor.obj x.D x.C X Unitor.unit) Y)
    (qR : Tensor.Slot x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y))
    (h : ((Tensor.slots x.D x.C X Unitor.unit).get qL.left).left ≠
      qR.left) :
    RealAssociator.homEntry X Unitor.unit Y qL qR =
      AtomHom.zero x.D _ _ := by
  unfold RealAssociator.homEntry
  rw [RealAssociatorLaws.realHomEntry_zero_of_left_ne
    X Unitor.unit Y qL qR h]
  exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

private theorem realAssociatorHomEntry_zero_of_middle_ne (X Y : Obj)
    (qL : Tensor.Slot x.D x.C (Tensor.obj x.D x.C X Unitor.unit) Y)
    (qR : Tensor.Slot x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y))
    (h : ((Tensor.slots x.D x.C X Unitor.unit).get qL.left).right ≠
      ((Tensor.slots x.D x.C Unitor.unit Y).get qR.right).left) :
    RealAssociator.homEntry X Unitor.unit Y qL qR =
      AtomHom.zero x.D _ _ := by
  unfold RealAssociator.homEntry
  rw [RealAssociatorLaws.realHomEntry_zero_of_middle_ne
    X Unitor.unit Y qL qR h]
  exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

private theorem realAssociatorHomEntry_zero_of_right_ne (X Y : Obj)
    (qL : Tensor.Slot x.D x.C (Tensor.obj x.D x.C X Unitor.unit) Y)
    (qR : Tensor.Slot x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y))
    (h : qL.right ≠
      ((Tensor.slots x.D x.C Unitor.unit Y).get qR.right).right) :
    RealAssociator.homEntry X Unitor.unit Y qL qR =
      AtomHom.zero x.D _ _ := by
  unfold RealAssociator.homEntry
  rw [RealAssociatorLaws.realHomEntry_zero_of_right_ne
    X Unitor.unit Y qL qR h]
  exact AtomHom.smul_zero realComputableShiftedRawDCT.laws.D _

/-- On an explicit middle-unit route, endpoint normalization contributes no
extra scalar, so the entry is the actual shifted connector coefficient. -/
private theorem realAssociatorHomEntry_route_coeff_middle_unit
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (targetABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label)) :
    (RealAssociator.homEntry X Unitor.unit Y
      (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
        i u j sourceAB sourceABC)
      (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
        i u j targetBC targetABC)).coeff
        (RealAssociatorLaws.routeAssocLabelEq X Unitor.unit Y
          i u j sourceAB sourceABC targetBC targetABC) =
      cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier)
          (RealAssociatorLaws.leftRouteSlot_label X Unitor.unit Y
            i u j sourceAB sourceABC).symm)
        (Associator.homCoefficient x (X.atom i).label 0
          (Y.atom j).label sourceAB sourceABC targetBC targetABC) := by
  unfold RealAssociator.homEntry
  rw [AtomHom.coeff_smul]
  rw [realAssociator_endpointSign_middle_unit]
  rw [(realComputableShiftedRawDCT.laws.D.algebra_laws _).one_smul]
  exact RealAssociatorLaws.realHomEntry_route_coeff
    X Unitor.unit Y i u j sourceAB sourceABC targetBC targetABC

/-- An explicit middle-unit associator entry vanishes when its transported
outer fusion rows differ. -/
private theorem realAssociatorHomEntry_zero_of_outer_ne
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (targetABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label))
    (hOuter :
      Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC ≠
        Associator.castIndex x rfl (zero_add (Y.atom j).label) targetABC) :
    RealAssociator.homEntry X Unitor.unit Y
        (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
          i u j sourceAB sourceABC)
        (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
          i u j targetBC targetABC) =
      AtomHom.zero x.D _ _ := by
  apply AtomHom.ext
  intro hLabel
  let hAssoc := RealAssociatorLaws.routeAssocLabelEq X Unitor.unit Y
    i u j sourceAB sourceABC targetBC targetABC
  have hh : hLabel = hAssoc := Subsingleton.elim _ _
  subst hh
  rw [realAssociatorHomEntry_route_coeff_middle_unit]
  rw [realComputableShifted_homCoefficient_middle_unit]
  have hRaw :
      Associator.castIndex rawX (add_zero (X.atom i).label) rfl sourceABC ≠
        Associator.castIndex rawX rfl (zero_add (Y.atom j).label)
          targetABC := by
    intro h
    apply hOuter
    apply Fin.ext
    simpa only [castIndex_val] using congrArg Fin.val h
  rw [if_neg hRaw]
  exact (cast_algebra_zero_of_label_eq_middle_unit x.D
    ((show ((X.atom i).label + 0 + (Y.atom j).label) =
        (Tensor.slotAtom x.D x.C (Tensor.obj x.D x.C X Unitor.unit) Y
          (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
            i u j sourceAB sourceABC)).label from
      (RealAssociatorLaws.leftRouteSlot_label X Unitor.unit Y
        i u j sourceAB sourceABC).symm))
    _).trans (AtomHom.coeff_zero hAssoc).symm

/-- For a fixed left middle-unit route, the actual associator has support at
the single right route with the same original positions and transported
outer row. -/
private theorem realAssociatorHomEntry_zero_unless_selected
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (selectedABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label))
    (hselected :
      Associator.castIndex x rfl (zero_add (Y.atom j).label) selectedABC =
        Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC)
    (qR : Tensor.Slot x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y))
    (hq : qR ≠ RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
      i u j targetBC selectedABC) :
    RealAssociator.homEntry X Unitor.unit Y
        (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
          i u j sourceAB sourceABC) qR =
      AtomHom.zero x.D _ _ := by
  rcases RealAssociatorLaws.exists_eq_rightRouteSlot
    X Unitor.unit Y qR with
    ⟨i', u', j', targetBC', targetABC', rfl⟩
  by_cases hi : i' = i
  · subst i'
    have hu : u' = u := Subsingleton.elim (α := Fin 1) u' u
    subst u'
    by_cases hj : j' = j
    · subst j'
      have hBC : targetBC' = targetBC :=
        (realUnitRowsLaws.left_unique (Y.atom j).label targetBC').trans
          (realUnitRowsLaws.left_unique (Y.atom j).label targetBC).symm
      subst targetBC'
      have hOuter :
          Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC ≠
            Associator.castIndex x rfl (zero_add (Y.atom j).label)
              targetABC' := by
        intro hmatch
        apply hq
        have hSelected : targetABC' = selectedABC := by
          apply castIndex_injective x rfl (zero_add (Y.atom j).label)
          exact hmatch.symm.trans hselected.symm
        subst targetABC'
        rfl
      exact realAssociatorHomEntry_zero_of_outer_ne
        X Y i u j sourceAB sourceABC targetBC targetABC' hOuter
    · apply realAssociatorHomEntry_zero_of_right_ne
      intro hcon
      apply hj
      have h1 := RealAssociatorLaws.rightRouteSlot_inner X Unitor.unit Y
        i u j' targetBC' targetABC'
      rw [h1] at hcon
      exact hcon.symm
  · apply realAssociatorHomEntry_zero_of_left_ne
    intro hcon
    apply hi
    have h1 := RealAssociatorLaws.leftRouteSlot_inner X Unitor.unit Y
      i u j sourceAB sourceABC
    rw [h1] at hcon
    exact hcon.symm

/-! ## Triangle on one explicit middle-unit route -/

/-- On the unique supported right route, composition with the left unitor
is the binary tensor block obtained from the strict right unitor.  The proof
is exactly the cancellation of the actual shifted connector scalar
`beta⁻¹` with the actual forward left-unitor scalar `beta`. -/
private theorem middleUnitSelectedComposite
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (selectedABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label))
    (hselected :
      Associator.castIndex x rfl (zero_add (Y.atom j).label) selectedABC =
        Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC)
    (targetAC : x.C.Index (X.atom i).label (Y.atom j).label) :
    AtomHom.comp
        (RealAssociator.homEntry X Unitor.unit Y
          (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
            i u j sourceAB sourceABC)
          (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
            i u j targetBC selectedABC))
        (Tensor.entry x.D x.C (Hom.id x.D X)
          (Unitor.leftHom x realUnitRowsData Y)
          (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
            i u j targetBC selectedABC)
          ⟨i, j, targetAC⟩) =
      Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y)
        (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
          i u j sourceAB sourceABC)
        ⟨i, j, targetAC⟩ := by
  let qL := RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
    i u j sourceAB sourceABC
  let qR := RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
    i u j targetBC selectedABC
  let qAC : Tensor.Slot x.D x.C X Y := ⟨i, j, targetAC⟩
  let hAssoc := RealAssociatorLaws.routeAssocLabelEq X Unitor.unit Y
    i u j sourceAB sourceABC targetBC selectedABC
  let hRight := middleRightRoute_binaryLabelEq X Y i u j
    targetBC selectedABC targetAC
  let hLeft := middleLeftRoute_binaryLabelEq X Y i u j
    sourceAB sourceABC targetAC
  let hTotal : (X.atom i).label + 0 + (Y.atom j).label =
      (X.atom i).label + (Y.atom j).label := by simp only [add_zero]
  change AtomHom.comp
      (RealAssociator.homEntry X Unitor.unit Y qL qR)
      (Tensor.entry x.D x.C (Hom.id x.D X)
        (Unitor.leftHom x realUnitRowsData Y) qR qAC) =
    Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y) qL qAC
  apply AtomHom.ext
  intro hLabel
  have hLabelComp : hLabel = hAssoc.trans hRight := Subsingleton.elim _ _
  rw [hLabelComp]
  apply cast_function_injective_middle_unit
    (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hLeft)
  have hTensorCast :
      cast (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hLeft)
          (cast
            (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hAssoc).symm
            ((Tensor.entry x.D x.C (Hom.id x.D X)
              (Unitor.leftHom x realUnitRowsData Y) qR qAC).coeff hRight)) =
        Tensor.coefficient x.D x.C
          (X.atom i).label (Y.atom j).label
          (X.atom i).shift (Y.atom j).shift (Y.atom j).shift
          (Associator.castIndex x rfl (zero_add (Y.atom j).label)
            selectedABC)
          targetAC (x.D.algebra (X.atom i).label).one
          (Unitor.leftHomCoefficient x realUnitRowsData
            (Y.atom j).label targetBC) := by
    rw [cast_cast_eq]
    calc
      cast
          (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier)
            (hAssoc.symm.trans hLeft))
          ((Tensor.entry x.D x.C (Hom.id x.D X)
            (Unitor.leftHom x realUnitRowsData Y) qR qAC).coeff hRight) =
        cast
          (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hRight)
          ((Tensor.entry x.D x.C (Hom.id x.D X)
            (Unitor.leftHom x realUnitRowsData Y) qR qAC).coeff hRight) :=
          cast_proof_irrel_middle_unit _ _ _
      _ = _ := middleRightTensorEntry_coeff X Y i u j
        targetBC selectedABC targetAC
  have hAssocCast :
      cast (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hLeft)
          ((RealAssociator.homEntry X Unitor.unit Y qL qR).coeff hAssoc) =
        cast
          (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hTotal)
          (Associator.homCoefficient x (X.atom i).label 0
            (Y.atom j).label sourceAB sourceABC targetBC selectedABC) := by
    rw [realAssociatorHomEntry_route_coeff_middle_unit]
    rw [cast_cast_eq]
    exact cast_proof_irrel_middle_unit _ _ _
  rw [AtomHom.coeff_comp _ _ hAssoc hRight]
  rw [cast_algebra_mul_of_label_eq x.D hLeft
    (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hLeft)]
  rw [hTensorCast, hAssocCast]
  calc
    (x.D.algebra ((X.atom i).label + (Y.atom j).label)).mul
        (Tensor.coefficient x.D x.C
          (X.atom i).label (Y.atom j).label
          (X.atom i).shift (Y.atom j).shift (Y.atom j).shift
          (Associator.castIndex x rfl (zero_add (Y.atom j).label)
            selectedABC)
          targetAC (x.D.algebra (X.atom i).label).one
          (Unitor.leftHomCoefficient x realUnitRowsData
            (Y.atom j).label targetBC))
        (cast
          (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hTotal)
          (Associator.homCoefficient x (X.atom i).label 0
            (Y.atom j).label sourceAB sourceABC targetBC selectedABC)) =
      (if targetAC =
            Associator.castIndex x rfl (zero_add (Y.atom j).label) selectedABC ∧
          Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC =
            Associator.castIndex x rfl (zero_add (Y.atom j).label) selectedABC
        then (x.D.algebra ((X.atom i).label + (Y.atom j).label)).one
        else (x.D.algebra ((X.atom i).label + (Y.atom j).label)).zero) :=
      middleUnitConvolutionTerm (X.atom i).label (Y.atom j).label
        (X.atom i).shift (Y.atom j).shift sourceAB sourceABC
        targetBC selectedABC targetAC
    _ = Tensor.coefficient x.D x.C
        (X.atom i).label (Y.atom j).label
        (X.atom i).shift (Y.atom j).shift (Y.atom j).shift
        (Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC)
        targetAC (x.D.algebra (X.atom i).label).one
        (x.D.algebra (Y.atom j).label).one := by
      rw [hselected]
      rw [Tensor.coefficient_one x.D
        realComputableShiftedRawDCT.laws.D x.C
        realComputableShiftedRawDCT.laws.C]
      simp
    _ = cast
        (congrArg (fun z : ZMod 8 => (x.D.algebra z).carrier) hLeft)
        ((Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y)
          qL qAC).coeff (hAssoc.trans hRight)) := by
      have hp : hAssoc.trans hRight = hLeft := Subsingleton.elim _ _
      rw [hp]
      exact (middleLeftTensorEntry_coeff X Y i u j
        sourceAB sourceABC targetAC).symm

/-- The categorical intermediate-slot sum has only the transported outer
row in its support.  This reduction uses the already proved connector
support theorem and performs no table evaluation. -/
private theorem middleUnitAssociatorTensor_sum_single
    (X Y : Obj) (i : Fin X.size) (u : Fin Unitor.unit.size)
    (j : Fin Y.size)
    (sourceAB : x.C.Index (X.atom i).label 0)
    (sourceABC : x.C.Index ((X.atom i).label + 0) (Y.atom j).label)
    (targetBC : x.C.Index 0 (Y.atom j).label)
    (selectedABC : x.C.Index (X.atom i).label (0 + (Y.atom j).label))
    (hselected :
      Associator.castIndex x rfl (zero_add (Y.atom j).label) selectedABC =
        Associator.castIndex x (add_zero (X.atom i).label) rfl sourceABC)
    (qAC : Tensor.Slot x.D x.C X Y) :
    AtomHom.finSum
        (Tensor.obj x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y)).size
        (fun m => AtomHom.comp
          (RealAssociator.homEntry X Unitor.unit Y
            (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
              i u j sourceAB sourceABC)
            ((Tensor.slots x.D x.C X
              (Tensor.obj x.D x.C Unitor.unit Y)).get m))
          (Tensor.entry x.D x.C (Hom.id x.D X)
            (Unitor.leftHom x realUnitRowsData Y)
            ((Tensor.slots x.D x.C X
              (Tensor.obj x.D x.C Unitor.unit Y)).get m) qAC)) =
      AtomHom.comp
        (RealAssociator.homEntry X Unitor.unit Y
          (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
            i u j sourceAB sourceABC)
          (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
            i u j targetBC selectedABC))
        (Tensor.entry x.D x.C (Hom.id x.D X)
          (Unitor.leftHom x realUnitRowsData Y)
          (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
            i u j targetBC selectedABC) qAC) := by
  let qSelected := RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
    i u j targetBC selectedABC
  let p : Fin (Tensor.obj x.D x.C X
      (Tensor.obj x.D x.C Unitor.unit Y)).size :=
    RealAssociatorLaws.slotPosition x.D x.C X
      (Tensor.obj x.D x.C Unitor.unit Y) qSelected
  rw [AtomHom.finSum_congr (g := fun m =>
      if m = p then
        AtomHom.comp
          (RealAssociator.homEntry X Unitor.unit Y
            (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
              i u j sourceAB sourceABC) qSelected)
          (Tensor.entry x.D x.C (Hom.id x.D X)
            (Unitor.leftHom x realUnitRowsData Y) qSelected qAC)
      else AtomHom.zero x.D _ _)]
  · exact AtomHom.finSum_single
      realComputableShiftedRawDCT.laws.D p _
  · intro m
    by_cases hm : m = p
    · subst m
      rw [RealAssociatorLaws.get_slotPosition]
      simp only [if_pos]
    · have hq :
          (Tensor.slots x.D x.C X
              (Tensor.obj x.D x.C Unitor.unit Y)).get m ≠ qSelected := by
        intro h
        apply hm
        apply slots_get_injective
        simpa only [p, qSelected, RealAssociatorLaws.get_slotPosition] using h
      rw [realAssociatorHomEntry_zero_unless_selected X Y i u j
        sourceAB sourceABC targetBC selectedABC hselected _ hq]
      rw [AtomHom.zero_comp realComputableShiftedRawDCT.laws.D]
      simp only [hm, if_false]

/-! ## The public triangle identity -/

/-- Triangle at one pair of source and target tensor slots. -/
private theorem realUnitor_triangle_entry (X Y : Obj)
    (qL : Tensor.Slot x.D x.C (Tensor.obj x.D x.C X Unitor.unit) Y)
    (qAC : Tensor.Slot x.D x.C X Y) :
    AtomHom.finSum
        (Tensor.obj x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y)).size
        (fun m => AtomHom.comp
          (RealAssociator.homEntry X Unitor.unit Y qL
            ((Tensor.slots x.D x.C X
              (Tensor.obj x.D x.C Unitor.unit Y)).get m))
          (Tensor.entry x.D x.C (Hom.id x.D X)
            (Unitor.leftHom x realUnitRowsData Y)
            ((Tensor.slots x.D x.C X
              (Tensor.obj x.D x.C Unitor.unit Y)).get m) qAC)) =
      Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y) qL qAC := by
  rcases RealAssociatorLaws.exists_eq_leftRouteSlot
    X Unitor.unit Y qL with ⟨i, u, j, sourceAB, sourceABC, rfl⟩
  let sourceAC := Associator.castIndex x
    (add_zero (X.atom i).label) rfl sourceABC
  let selectedABC := Associator.castIndex x rfl
    (zero_add (Y.atom j).label).symm sourceAC
  let targetBC := realUnitRowsData.left (Y.atom j).label
  have hselected :
      Associator.castIndex x rfl (zero_add (Y.atom j).label) selectedABC =
        sourceAC := by
    apply Fin.ext
    simp only [selectedABC, castIndex_val]
  rw [middleUnitAssociatorTensor_sum_single X Y i u j
    sourceAB sourceABC targetBC selectedABC hselected qAC]
  rcases qAC with ⟨i', j', targetAC⟩
  by_cases hi : i' = i
  · subst i'
    by_cases hj : j' = j
    · subst j'
      exact middleUnitSelectedComposite X Y i u j sourceAB sourceABC
        targetBC selectedABC hselected targetAC
    · have hTensorRight :
          Tensor.entry x.D x.C (Hom.id x.D X)
              (Unitor.leftHom x realUnitRowsData Y)
              (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
                i u j targetBC selectedABC)
              ⟨i, j', targetAC⟩ = AtomHom.zero x.D _ _ := by
        apply Tensor.entry_of_right_eq_zero x.D
          realComputableShiftedRawDCT.laws.D x.C
          realComputableShiftedRawDCT.laws.C
        have hgen : ∀ (sl : Tensor.Slot x.D x.C Unitor.unit Y)
            (_hsl : sl = ⟨u, j, targetBC⟩),
            Unitor.leftHomEntry x realUnitRowsData Y sl
              (Tensor.Slot.right (⟨i, j', targetAC⟩ :
                Tensor.Slot x.D x.C X Y)) =
            AtomHom.zero x.D _ _ := by
          intro sl hsl
          subst hsl
          unfold Unitor.leftHomEntry
          rw [dif_neg (show ¬ Tensor.Slot.right
              (⟨u, j, targetBC⟩ : Tensor.Slot x.D x.C Unitor.unit Y) =
              Tensor.Slot.right (⟨i, j', targetAC⟩ :
                Tensor.Slot x.D x.C X Y) from
            fun hcon => hj hcon.symm)]
        exact hgen ((Tensor.slots x.D x.C Unitor.unit Y).get
            (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
              i u j targetBC selectedABC).right)
          (RealAssociatorLaws.rightRouteSlot_inner X Unitor.unit Y
            i u j targetBC selectedABC)
      have hTensorLeft :
          Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y)
              (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
                i u j sourceAB sourceABC)
              ⟨i, j', targetAC⟩ = AtomHom.zero x.D _ _ := by
        apply Tensor.entry_of_right_eq_zero x.D
          realComputableShiftedRawDCT.laws.D x.C
          realComputableShiftedRawDCT.laws.C
        simp [Hom.id, RealAssociatorLaws.leftRouteSlot_right,
          Ne.symm hj]
        intro h
        exact absurd h.symm hj
      rw [hTensorRight,
        AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
        hTensorLeft]
  · have hTensorRight :
        Tensor.entry x.D x.C (Hom.id x.D X)
            (Unitor.leftHom x realUnitRowsData Y)
            (RealAssociatorLaws.rightRouteSlot X Unitor.unit Y
              i u j targetBC selectedABC)
            ⟨i', j', targetAC⟩ = AtomHom.zero x.D _ _ := by
      apply Tensor.entry_of_left_eq_zero x.D
        realComputableShiftedRawDCT.laws.D x.C
        realComputableShiftedRawDCT.laws.C
      simp [Hom.id, RealAssociatorLaws.rightRouteSlot_left, Ne.symm hi]
      intro h
      exact absurd h.symm hi
    have hTensorLeft :
        Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y)
            (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
              i u j sourceAB sourceABC)
            ⟨i', j', targetAC⟩ = AtomHom.zero x.D _ _ := by
      apply Tensor.entry_of_left_eq_zero x.D
        realComputableShiftedRawDCT.laws.D x.C
        realComputableShiftedRawDCT.laws.C
      have hgen : ∀ (sl : Tensor.Slot x.D x.C X Unitor.unit)
          (_hsl : sl = ⟨i, u, sourceAB⟩),
          Unitor.rightHomEntry x X sl
            (Tensor.Slot.left (⟨i', j', targetAC⟩ :
              Tensor.Slot x.D x.C X Y)) =
          AtomHom.zero x.D _ _ := by
        intro sl hsl
        subst hsl
        unfold Unitor.rightHomEntry
        rw [dif_neg (show ¬ Tensor.Slot.left
            (⟨i, u, sourceAB⟩ : Tensor.Slot x.D x.C X Unitor.unit) =
            Tensor.Slot.left (⟨i', j', targetAC⟩ :
              Tensor.Slot x.D x.C X Y) from
          fun hcon => hi hcon.symm)]
      exact hgen ((Tensor.slots x.D x.C X Unitor.unit).get
          (RealAssociatorLaws.leftRouteSlot X Unitor.unit Y
            i u j sourceAB sourceABC).left)
        (RealAssociatorLaws.leftRouteSlot_inner X Unitor.unit Y
          i u j sourceAB sourceABC)
    rw [hTensorRight,
      AtomHom.comp_zero realComputableShiftedRawDCT.laws.D,
      hTensorLeft]

/-- The exact endpoint-normalized associator and the exact unitors extracted
from the shifted real raw DCT satisfy the triangle identity. -/
theorem realUnitor_triangle (X Y : Obj) :
    Hom.comp (RealAssociator.hom X Unitor.unit Y)
        (Tensor.hom x.D x.C (Hom.id x.D X)
          (Unitor.leftHom x realUnitRowsData Y)) =
      Tensor.hom x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y) := by
  apply Hom.ext
  intro i k
  let qL := (Tensor.slots x.D x.C
    (Tensor.obj x.D x.C X Unitor.unit) Y).get i
  let qAC := (Tensor.slots x.D x.C X Y).get k
  unfold Hom.comp RealAssociator.hom Tensor.hom
  change AtomHom.finSum
      (Tensor.obj x.D x.C X (Tensor.obj x.D x.C Unitor.unit Y)).size
      (fun m => AtomHom.comp
        (RealAssociator.homEntry X Unitor.unit Y qL
          ((Tensor.slots x.D x.C X
            (Tensor.obj x.D x.C Unitor.unit Y)).get m))
        (Tensor.entry x.D x.C (Hom.id x.D X)
          (Unitor.leftHom x realUnitRowsData Y)
          ((Tensor.slots x.D x.C X
            (Tensor.obj x.D x.C Unitor.unit Y)).get m) qAC)) =
    Tensor.entry x.D x.C (Unitor.rightHom x X) (Hom.id x.D Y) qL qAC
  exact realUnitor_triangle_entry X Y qL qAC

/-! ## Completed concrete unitor laws -/

/-- All inverse, parity, naturality, and triangle laws for the exact unitors
read from the computably shifted real raw DCT. -/
def realUnitorLaws : UnitorLaws
    RealPairing.realD.data RealPairing.realD.laws
    RealPairing.realTensor.data RealPairing.realTensor.laws
    realAssociatorData realAssociatorLaws
    (Unitor.canonicalData x realUnitRowsData) where
  leftUnitor_hom_inv := realLeftUnitor_hom_inv
  leftUnitor_inv_hom := realLeftUnitor_inv_hom
  leftUnitor_hom_even := realLeftUnitor_hom_even
  leftUnitor_inv_even := realLeftUnitor_inv_even
  leftUnitor_naturality := realLeftUnitor_naturality
  rightUnitor_hom_inv := realRightUnitor_hom_inv
  rightUnitor_inv_hom := realRightUnitor_inv_hom
  rightUnitor_hom_even := realRightUnitor_hom_even
  rightUnitor_inv_even := realRightUnitor_inv_even
  rightUnitor_naturality := realRightUnitor_naturality
  triangle := realUnitor_triangle

end Superfusion.RMod.FromRawDCT
