import Superfusion.RMod.RawDCT.C
import Superfusion.RMod.RawDCT.RealD
import Superfusion.RMod.Constructive.FusionTableData
import Superfusion.RMod.Constructive.FusionTableLaws

/-!
# Concrete computable real fusion kernels

This file instantiates the abstract `CData`/`CLaws`/`C` layers for the raw
real fusion tables.  The data layer is the literal finite coordinate module
and its table-driven left action.  All semantic and algebraic arguments are
confined to the subsequent law layer.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

open RModCoordinate
open RModCoordinate.FusionTable

/-! ## Data -/

/-- The concrete finite right-module carrier at a pair of labels. -/
abbrev RealCCarrier (a b : ZMod 8) : Type :=
  RModCoordinate.FusionTable.Index a b → Coeff (a + b)

def realCZero (a b : ZMod 8) : RealCCarrier a b :=
  fun _ => Coeff.zero (a + b)

def realCAdd (a b : ZMod 8) (x y : RealCCarrier a b) : RealCCarrier a b :=
  fun row => Coeff.add (a + b) (x row) (y row)

def realCNeg (a b : ZMod 8) (x : RealCCarrier a b) : RealCCarrier a b :=
  fun row => Coeff.neg (a + b) (x row)

def realCSmul (a b : ZMod 8) (q : ℝ) (x : RealCCarrier a b) :
    RealCCarrier a b :=
  fun row => Coeff.smul (a + b) q (x row)

def realCComponent (a b : ZMod 8) (i : ZMod 2) (x : RealCCarrier a b) :
    RealCCarrier a b :=
  fun row => Coeff.component (a + b) (i + indexParity a b row) (x row)

/-- The table-driven action of a pure pair of coefficient-algebra elements. -/
def realCLeft (a b : ZMod 8) (x : Coeff a) (y : Coeff b)
    (m : RealCCarrier a b) : RealCCarrier a b :=
  fun target =>
    CData.rawFinSum (realDData.algebra (a + b)) fun source =>
      Coeff.mul (a + b) (fusionCoefficient a b target source x y) (m source)

/-- Pointwise right multiplication by the endpoint coefficient algebra. -/
def realCRight (a b : ZMod 8) (m : RealCCarrier a b) (x : Coeff (a + b)) :
    RealCCarrier a b :=
  fun row => Coeff.mul (a + b) (m row) x

/-- The complete executable real fusion-kernel data. -/
def realCData : CData realDData where
  rank := fun a b => (realSize a b).1 + (realSize a b).2
  rowParity := indexParity
  leftCoeff := fusionCoefficient
  carrier := RealCCarrier
  toCoord := fun _ _ x => x
  ofCoord := fun _ _ x => x
  zero := realCZero
  add := realCAdd
  neg := realCNeg
  smul := realCSmul
  component := realCComponent
  left := realCLeft
  right := realCRight

example : realCData.rank 1 3 = 2 := rfl

example : realCData.rowParity 1 3
    (⟨1, by change 1 < 2; omega⟩ : realCData.Index 1 3) = 1 := rfl

/-! ## Private finite-sum bridges used by the law layer -/

private theorem realRawFinSum_eq_sum {a : ZMod 8} {n : ℕ}
    (f : Fin n → Coeff a) :
    CData.rawFinSum (realDData.algebra a) f = ∑ r, f r := by
  change (List.ofFn f).sum = ∑ r, f r
  exact List.sum_ofFn

private theorem coeff_mul_sum {I : Type*} [Fintype I] (a : ZMod 8)
    (x : Coeff a) (f : I → Coeff a) :
    Coeff.mul a x (∑ r, f r) = ∑ r, Coeff.mul a x (f r) := by
  apply (Coeff.semantic a).injective
  simpa only [map_sum, Coeff.semantic_mul] using
    (Finset.mul_sum (s := Finset.univ) (fun r => Coeff.semantic a (f r))
      (Coeff.semantic a x))

private theorem coeff_sum_mul {I : Type*} [Fintype I] (a : ZMod 8)
    (f : I → Coeff a) (x : Coeff a) :
    Coeff.mul a (∑ r, f r) x = ∑ r, Coeff.mul a (f r) x := by
  apply (Coeff.semantic a).injective
  simpa only [map_sum, Coeff.semantic_mul] using
    (Finset.sum_mul (s := Finset.univ) (fun r => Coeff.semantic a (f r))
      (Coeff.semantic a x))

private theorem coeff_smul_sum {I : Type*} [Fintype I] (a : ZMod 8)
    (q : ℝ) (f : I → Coeff a) :
    Coeff.smul a q (∑ r, f r) = ∑ r, Coeff.smul a q (f r) := by
  ext g
  simp only [Coeff.smul, Finset.sum_apply]
  exact Finset.mul_sum (s := Finset.univ) (fun r => f r g) q

private theorem coeff_sum_zero {I : Type*} [Fintype I] (a : ZMod 8) :
    (∑ _ : I, Coeff.zero a) = Coeff.zero a := by
  ext g
  simp [Coeff.zero]

private theorem coeff_sum_memGrade {I : Type*} [Fintype I]
    (a : ZMod 8) (i : ZMod 2) (f : I → Coeff a)
    (hf : ∀ r, Coeff.MemGrade a i (f r)) :
    Coeff.MemGrade a i (∑ r, f r) := by
  intro g hg
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun r _ => hf r g hg

/-- The integer-unit sign used by the semantic table certificate is the
public real parity sign used by `CLaws`. -/
private theorem intSgnCast_eq_paritySign (i : ZMod 2) :
    ((((sgn i : ℤˣ) : ℤ) : ℝ)) = paritySign i := by
  rcases zmod2_cases i with rfl | rfl <;> simp [paritySign]

private theorem fusionCoefficient_mul_parity (a b : ZMod 8) (i j : ZMod 2)
    (target source : RModCoordinate.FusionTable.Index a b)
    (x x' : Coeff a) (y y' : Coeff b)
    (hy : Coeff.MemGrade b j y) (hx' : Coeff.MemGrade a i x') :
    (∑ middle : RModCoordinate.FusionTable.Index a b,
        Coeff.mul (a + b)
          (fusionCoefficient a b target middle x y)
          (fusionCoefficient a b middle source x' y')) =
      Coeff.smul (a + b) (paritySign (j * i))
        (fusionCoefficient a b target source
          (Coeff.mul a x x') (Coeff.mul b y y')) := by
  simpa only [intSgnCast_eq_paritySign] using
    (FusionTableLaws.fusionCoefficient_mul a b i j target source
      (x := x) (x' := x') (y := y) (y' := y') hy hx')

private theorem realCLeft_mul (a b : ZMod 8) (i j : ZMod 2)
    (x x' : Coeff a) (y y' : Coeff b) (m : RealCCarrier a b)
    (hy : Coeff.MemGrade b j y) (hx' : Coeff.MemGrade a i x') :
    realCLeft a b x y (realCLeft a b x' y' m) =
      realCSmul a b (paritySign (j * i))
        (realCLeft a b (Coeff.mul a x x') (Coeff.mul b y y') m) := by
  funext target
  unfold realCLeft realCSmul
  simp_rw [realRawFinSum_eq_sum]
  calc
    (∑ middle,
        Coeff.mul (a + b) (fusionCoefficient a b target middle x y)
          (∑ source,
            Coeff.mul (a + b) (fusionCoefficient a b middle source x' y')
              (m source))) =
        ∑ middle, ∑ source,
          Coeff.mul (a + b) (fusionCoefficient a b target middle x y)
            (Coeff.mul (a + b) (fusionCoefficient a b middle source x' y')
              (m source)) := by
          apply Finset.sum_congr rfl
          intro middle _
          exact coeff_mul_sum (a + b)
            (fusionCoefficient a b target middle x y) _
    _ = ∑ source, ∑ middle,
          Coeff.mul (a + b)
            (Coeff.mul (a + b) (fusionCoefficient a b target middle x y)
              (fusionCoefficient a b middle source x' y'))
            (m source) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro source _
          apply Finset.sum_congr rfl
          intro middle _
          exact (Coeff.mul_assoc (a + b) _ _ _).symm
    _ = ∑ source,
          Coeff.mul (a + b)
            (∑ middle,
              Coeff.mul (a + b) (fusionCoefficient a b target middle x y)
                (fusionCoefficient a b middle source x' y'))
            (m source) := by
          apply Finset.sum_congr rfl
          intro source _
          exact (coeff_sum_mul (a + b) _ (m source)).symm
    _ = ∑ source,
          Coeff.mul (a + b)
            (Coeff.smul (a + b) (paritySign (j * i))
              (fusionCoefficient a b target source
                (Coeff.mul a x x') (Coeff.mul b y y')))
            (m source) := by
          apply Finset.sum_congr rfl
          intro source _
          rw [fusionCoefficient_mul_parity a b i j target source x x' y y' hy hx']
    _ = ∑ source,
          Coeff.smul (a + b) (paritySign (j * i))
            (Coeff.mul (a + b)
              (fusionCoefficient a b target source
                (Coeff.mul a x x') (Coeff.mul b y y'))
              (m source)) := by
          apply Finset.sum_congr rfl
          intro source _
          exact Coeff.smul_mul (a + b) _ _ _
    _ = Coeff.smul (a + b) (paritySign (j * i))
          (∑ source,
            Coeff.mul (a + b)
              (fusionCoefficient a b target source
                (Coeff.mul a x x') (Coeff.mul b y y'))
              (m source)) :=
      (coeff_smul_sum (a + b) (paritySign (j * i)) _).symm

private theorem realCLeft_memGrade (a b : ZMod 8) (i j k : ZMod 2)
    (x : Coeff a) (y : Coeff b) (m : RealCCarrier a b)
    (hx : Coeff.MemGrade a i x) (hy : Coeff.MemGrade b j y)
    (hm : CData.MemGrade realCData a b k m) :
    CData.MemGrade realCData a b (i + j + k) (realCLeft a b x y m) := by
  apply funext
  intro target
  apply (Coeff.component_eq_self_iff (a + b)
    (i + j + k + indexParity a b target) _).2
  unfold realCLeft
  rw [realRawFinSum_eq_sum]
  apply coeff_sum_memGrade
  intro source
  have hmSource : Coeff.MemGrade (a + b)
      (k + indexParity a b source) (m source) := by
    apply (Coeff.component_eq_self_iff (a + b)
      (k + indexParity a b source) _).1
    have h := congrFun hm source
    exact h
  have hproduct := Coeff.memGrade_mul (a + b)
    (i + j + indexParity a b target + indexParity a b source)
    (k + indexParity a b source)
    (FusionTableLaws.fusionCoefficient_memGrade a b i j target source hx hy)
    hmSource
  have hdegree :
      (i + j + indexParity a b target + indexParity a b source) +
          (k + indexParity a b source) =
        i + j + k + indexParity a b target := by
    calc
      _ = i + j + k + indexParity a b target +
          (indexParity a b source + indexParity a b source) := by abel
      _ = i + j + k + indexParity a b target := by
        rw [Coeff.add_self_eq_zero, add_zero]
  exact hdegree ▸ hproduct

private theorem realCActions_comm (a b : ZMod 8) (x : Coeff a) (y : Coeff b)
    (m : RealCCarrier a b) (z : Coeff (a + b)) :
    realCRight a b (realCLeft a b x y m) z =
      realCLeft a b x y (realCRight a b m z) := by
  funext target
  unfold realCRight realCLeft
  simp_rw [realRawFinSum_eq_sum]
  rw [coeff_sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  exact Coeff.mul_assoc (a + b) _ _ _

/-! ## Laws and completed bundle -/

/-- The laws of the concrete real fusion-kernel data. -/
theorem realCLaws : CLaws realDData realDLaws realCData where
  ofCoord_toCoord := by
    intro a b x
    rfl
  toCoord_ofCoord := by
    intro a b x
    rfl
  toCoord_zero := by
    intro a b
    rfl
  toCoord_add := by
    intro a b x y
    rfl
  toCoord_neg := by
    intro a b x
    rfl
  toCoord_smul := by
    intro a b q x
    rfl
  toCoord_component := by
    intro a b i x
    rfl
  toCoord_left := by
    intro a b x y m
    rfl
  toCoord_right := by
    intro a b m x
    rfl

  add_assoc := by
    intro a b x y z
    funext row
    exact Coeff.add_assoc (a + b) (x row) (y row) (z row)
  add_comm := by
    intro a b x y
    funext row
    exact Coeff.add_comm (a + b) (x row) (y row)
  zero_add := by
    intro a b x
    funext row
    exact Coeff.zero_add (a + b) (x row)
  add_zero := by
    intro a b x
    funext row
    exact Coeff.add_zero (a + b) (x row)
  neg_add := by
    intro a b x
    funext row
    exact Coeff.neg_add (a + b) (x row)
  add_neg := by
    intro a b x
    funext row
    exact Coeff.add_neg (a + b) (x row)
  one_smul := by
    intro a b x
    funext row
    exact Coeff.one_smul (a + b) (x row)
  smul_assoc := by
    intro a b r s x
    funext row
    exact Coeff.mul_smul (a + b) r s (x row)
  add_smul := by
    intro a b r s x
    funext row
    exact Coeff.add_smul (a + b) r s (x row)
  smul_add := by
    intro a b r x y
    funext row
    exact Coeff.smul_add (a + b) r (x row) (y row)
  zero_smul := by
    intro a b x
    funext row
    exact Coeff.zero_smul (a + b) (x row)
  smul_zero := by
    intro a b r
    funext row
    exact Coeff.smul_zero (a + b) r

  component_zero := by
    intro a b i
    funext row
    exact Coeff.component_zero (a + b) (i + indexParity a b row)
  component_add := by
    intro a b i x y
    funext row
    exact Coeff.component_add (a + b) (i + indexParity a b row) (x row) (y row)
  component_neg := by
    intro a b i x
    funext row
    exact Coeff.component_neg (a + b) (i + indexParity a b row) (x row)
  component_smul := by
    intro a b i r x
    funext row
    exact Coeff.component_smul (a + b) (i + indexParity a b row) r (x row)
  component_idem := by
    intro a b i x
    funext row
    exact Coeff.component_idem (a + b) (i + indexParity a b row) (x row)
  component_complement := by
    intro a b i x
    funext row
    change Coeff.add (a + b)
      (Coeff.component (a + b) (i + indexParity a b row) (x row))
      (Coeff.component (a + b) (i + 1 + indexParity a b row) (x row)) = x row
    simpa [add_assoc, add_comm, add_left_comm] using
      (Coeff.component_complement (a + b) (i + indexParity a b row) (x row))
  grade_disjoint := by
    intro a b i x hx hx'
    funext row
    apply Coeff.memGrade_disjoint (a + b) (i + indexParity a b row)
    · apply (Coeff.component_eq_self_iff (a + b)
        (i + indexParity a b row) (x row)).1
      have h := congrFun hx row
      change Coeff.component (a + b) (i + indexParity a b row) (x row) = x row at h
      exact h
    · apply (Coeff.component_eq_self_iff (a + b)
        (i + indexParity a b row + 1) (x row)).1
      have h := congrFun hx' row
      change Coeff.component (a + b) (i + 1 + indexParity a b row) (x row) = x row at h
      simpa [add_assoc, add_comm, add_left_comm] using h

  left_zero_left := by
    intro a b y m
    change realCLeft a b (Coeff.zero a) y m = realCZero a b
    funext target
    unfold realCLeft realCZero
    rw [realRawFinSum_eq_sum]
    simp_rw [FusionTableLaws.fusionCoefficient_zero_left, Coeff.zero_mul]
    exact coeff_sum_zero (a + b)
  left_zero_right := by
    intro a b x m
    change realCLeft a b x (Coeff.zero b) m = realCZero a b
    funext target
    unfold realCLeft realCZero
    rw [realRawFinSum_eq_sum]
    simp_rw [FusionTableLaws.fusionCoefficient_zero_right, Coeff.zero_mul]
    exact coeff_sum_zero (a + b)
  left_zero_module := by
    intro a b x y
    change realCLeft a b x y (realCZero a b) = realCZero a b
    funext target
    unfold realCLeft realCZero
    rw [realRawFinSum_eq_sum]
    simp_rw [Coeff.mul_zero]
    exact coeff_sum_zero (a + b)
  left_add_left := by
    intro a b x x' y m
    change realCLeft a b (Coeff.add a x x') y m =
      realCAdd a b (realCLeft a b x y m) (realCLeft a b x' y m)
    funext target
    unfold realCLeft realCAdd
    simp_rw [realRawFinSum_eq_sum,
      FusionTableLaws.fusionCoefficient_add_left, Coeff.add_mul]
    exact Finset.sum_add_distrib
  left_add_right := by
    intro a b x y y' m
    change realCLeft a b x (Coeff.add b y y') m =
      realCAdd a b (realCLeft a b x y m) (realCLeft a b x y' m)
    funext target
    unfold realCLeft realCAdd
    simp_rw [realRawFinSum_eq_sum,
      FusionTableLaws.fusionCoefficient_add_right, Coeff.add_mul]
    exact Finset.sum_add_distrib
  left_add_module := by
    intro a b x y m m'
    change realCLeft a b x y (realCAdd a b m m') =
      realCAdd a b (realCLeft a b x y m) (realCLeft a b x y m')
    funext target
    unfold realCLeft realCAdd
    simp_rw [realRawFinSum_eq_sum, Coeff.mul_add]
    exact Finset.sum_add_distrib
  left_smul_left := by
    intro a b r x y m
    change realCLeft a b (Coeff.smul a r x) y m =
      realCSmul a b r (realCLeft a b x y m)
    funext target
    unfold realCLeft realCSmul
    simp_rw [realRawFinSum_eq_sum,
      FusionTableLaws.fusionCoefficient_smul_left, Coeff.smul_mul]
    exact (coeff_smul_sum (a + b) r _).symm
  left_smul_right := by
    intro a b r x y m
    change realCLeft a b x (Coeff.smul b r y) m =
      realCSmul a b r (realCLeft a b x y m)
    funext target
    unfold realCLeft realCSmul
    simp_rw [realRawFinSum_eq_sum,
      FusionTableLaws.fusionCoefficient_smul_right, Coeff.smul_mul]
    exact (coeff_smul_sum (a + b) r _).symm
  left_smul_module := by
    intro a b r x y m
    change realCLeft a b x y (realCSmul a b r m) =
      realCSmul a b r (realCLeft a b x y m)
    funext target
    unfold realCLeft realCSmul
    simp_rw [realRawFinSum_eq_sum, Coeff.mul_smul_right]
    exact (coeff_smul_sum (a + b) r _).symm
  left_one := by
    intro a b m
    change realCLeft a b (Coeff.one a) (Coeff.one b) m = m
    funext target
    unfold realCLeft
    rw [realRawFinSum_eq_sum]
    simp_rw [FusionTableLaws.fusionCoefficient_one]
    rw [Fintype.sum_eq_single target]
    · simp [Coeff.one_mul]
    · intro source hsource
      rw [if_neg (Ne.symm hsource), Coeff.zero_mul]
      rfl
  left_mul := by
    intro a b i j x x' y y' m hy hx'
    apply realCLeft_mul a b i j x x' y y' m
    · exact (Coeff.component_eq_self_iff b j y).1 hy
    · exact (Coeff.component_eq_self_iff a i x').1 hx'
  left_memGrade := by
    intro a b i j k x y m hx hy hm
    apply realCLeft_memGrade a b i j k x y m
    · exact (Coeff.component_eq_self_iff a i x).1 hx
    · exact (Coeff.component_eq_self_iff b j y).1 hy
    · exact hm

  right_zero_module := by
    intro a b x
    funext row
    exact Coeff.zero_mul (a + b) x
  right_zero_algebra := by
    intro a b m
    funext row
    exact Coeff.mul_zero (a + b) (m row)
  right_add_module := by
    intro a b m m' x
    funext row
    exact Coeff.add_mul (a + b) (m row) (m' row) x
  right_add_algebra := by
    intro a b m x x'
    funext row
    exact Coeff.mul_add (a + b) (m row) x x'
  right_smul_module := by
    intro a b r m x
    funext row
    exact Coeff.smul_mul (a + b) r (m row) x
  right_smul_algebra := by
    intro a b r m x
    funext row
    exact Coeff.mul_smul_right (a + b) r (m row) x
  right_one := by
    intro a b m
    funext row
    exact Coeff.mul_one (a + b) (m row)
  right_assoc := by
    intro a b m x y
    funext row
    exact Coeff.mul_assoc (a + b) (m row) x y
  right_memGrade := by
    intro a b i j m x hm hx
    funext row
    apply (Coeff.component_eq_self_iff (a + b)
      (i + j + indexParity a b row) _).2
    have hmRow : Coeff.MemGrade (a + b)
        (i + indexParity a b row) (m row) := by
      apply (Coeff.component_eq_self_iff (a + b)
        (i + indexParity a b row) _).1
      exact congrFun hm row
    have hx' : Coeff.MemGrade (a + b) j x :=
      (Coeff.component_eq_self_iff (a + b) j x).1 hx
    change Coeff.MemGrade (a + b) (i + j + indexParity a b row)
      (Coeff.mul (a + b) (m row) x)
    simpa [add_assoc, add_comm, add_left_comm] using
      (Coeff.memGrade_mul (a + b)
        (i + indexParity a b row) j hmRow hx')

  actions_comm := by
    intro a b x y m z
    exact realCActions_comm a b x y m z

/-- The completed raw real fusion-kernel family. -/
def realC : C realD where
  data := realCData
  laws := realCLaws

end Superfusion.RMod.RawDCT
