import Mathlib.Data.List.NodupEquivFin
import Superfusion.Category.ExactPairingBiproduct
import Superfusion.Category.ExactPairingCoordinateDetection
import Superfusion.RMod.FromRawDCT.MathlibAdapter
import Superfusion.RMod.FromRawDCT.PairingAdapter
import Superfusion.RMod.FromRawDCT.RealSemisimple

/-!
# Exact pairings for the shifted real coordinate atoms

This concrete instance file constructs duality directly in the finite
coordinate envelope of `realComputableShiftedRawDCT`.  Its input is the
already shifted raw `D`, `C`, and `T`; it does not transport a semantic
`RModCarrier` pairing.

The first stage below is independent of monoidal coherence.  It identifies
the even inverse-label row, constructs its split coordinate inclusion, and
builds the homogeneous singleton comparisons used by supermultiplicity.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open RawDCT

namespace RealPairing

/-! ## Concrete completed binary data -/

/-- The completed coefficient-algebra family of the shifted real raw DCT. -/
def realD : D where
  data := realComputableShiftedRawDCT.data.D
  laws := realComputableShiftedRawDCT.laws.D

/-- The completed shifted real binary fusion kernel. -/
def realC : C realD where
  data := realComputableShiftedRawDCT.data.C
  laws := realComputableShiftedRawDCT.laws.C

/-- The canonical computable tensor bifunctor of the shifted real kernel. -/
def realTensor : Tensor realD :=
  Tensor.canonical realD realC

local instance realCategory : Category Obj :=
  MathlibAdapter.category realD

local instance realPreadditive : Preadditive Obj :=
  MathlibAdapter.preadditive realD

local instance realLinear : Linear ℝ Obj :=
  MathlibAdapter.linear realD

local instance realSupercategory : Superfusion.Category.Supercategory ℝ Obj :=
  MathlibAdapter.supercategory realD

local instance realDLawsFact : Fact (DLaws realD.data) :=
  ⟨realD.laws⟩

noncomputable local instance realEvenBiproducts :
    HasFiniteBiproducts (Superfusion.Category.EvenSubcategory ℝ Obj) :=
  MathlibAdapter.evenHasFiniteBiproducts
    realComputableShiftedRawDCT.data realD.laws realUnitRowsData

/-! ## The distinguished inverse-label row -/

/-- The shifted right-dual atom.  Its shift cancels the binary cochain on
the inverse-label tensor face. -/
def rightDualAtom (A : Atom) : Atom :=
  (-A.label,
    A.shift + shiftNu realComputableShiftData.cochains
      A.label (-A.label))

/-- The analogous left-dual atom. -/
def leftDualAtom (A : Atom) : Atom :=
  (-A.label,
    A.shift + shiftNu realComputableShiftData.cochains
      (-A.label) A.label)

/-- Applying the right-dual prescription to the chosen left dual returns
the original atom. -/
theorem rightDual_leftDual (A : Atom) :
    rightDualAtom (leftDualAtom A) = A := by
  rcases A with ⟨a, s⟩
  change
    (- -a,
      (s + shiftNu realComputableShiftData.cochains (-a) a) +
        shiftNu realComputableShiftData.cochains (-a) (- -a)) = (a, s)
  rw [neg_neg]
  apply Prod.ext
  · rfl
  · change
      (s + shiftNu realComputableShiftData.cochains (-a) a) +
        shiftNu realComputableShiftData.cochains (-a) a = s
    rw [add_assoc, ZModModule.add_self, add_zero]

/-- Every inverse-label real fusion table has a nonzero even block.  This is
only the eight-entry size lookup; no ternary or fourfold tensor calculation
is involved. -/
theorem inverseEvenMultiplicity_pos (a : ZMod 8) :
    0 < (realSize a (-a)).1 := by
  fin_cases a <;> decide

/-- The first row of the even block on the `(a,-a)` fusion face. -/
def inverseEvenRow (a : ZMod 8) : realC.data.Index a (-a) :=
  ⟨0, by
    change 0 < (realSize a (-a)).1 + (realSize a (-a)).2
    have hp := inverseEvenMultiplicity_pos a
    omega⟩

/-- At that first row the shifted stored parity is exactly the binary
cochain used in the dual shift. -/
theorem inverseEvenRow_parity (a : ZMod 8) :
    realC.data.rowParity a (-a) (inverseEvenRow a) =
      shiftNu realComputableShiftData.cochains a (-a) := by
  fin_cases a <;> rfl

/-! ## Locating the row inside the canonical tensor enumeration -/

private theorem slots_mem_all (dD : DData) (dC : CData dD)
    (X Y : Obj) (q : Tensor.Slot dD dC X Y) :
    q ∈ Tensor.slots dD dC X Y := by
  rcases q with ⟨i, j, r⟩
  simp [Tensor.slots]

/-- The canonical slot list, viewed as an equivalence with its index type. -/
private def slotsEquiv (dD : DData) (dC : CData dD) (X Y : Obj) :
    Fin (Tensor.slots dD dC X Y).length ≃ Tensor.Slot dD dC X Y :=
  (Tensor.slots_nodup dD dC X Y).getEquivOfForallMemList
    (Tensor.slots dD dC X Y) (slots_mem_all dD dC X Y)

/-- The inverse-label even slot in the tensor of a singleton atom with its
chosen right dual. -/
def rightDualSlot (A : Atom) :
    Tensor.Slot realD.data realC.data
      (Obj.singleton A) (Obj.singleton (rightDualAtom A)) :=
  ⟨Finite.singletonIndex A,
    Finite.singletonIndex (rightDualAtom A), inverseEvenRow A.label⟩

/-- The index of the distinguished slot in the tensor object. -/
def rightDualSlotIndex (A : Atom) :
    Fin (Tensor.obj realD.data realC.data
      (Obj.singleton A) (Obj.singleton (rightDualAtom A))).size :=
  (slotsEquiv realD.data realC.data
    (Obj.singleton A) (Obj.singleton (rightDualAtom A))).symm
      (rightDualSlot A)

private theorem zmod2_add_self (s : ZMod 2) : s + s = 0 :=
  ZModModule.add_self s

/-- The distinguished tensor summand is literally the unshifted unit atom. -/
theorem rightDualSlot_atom (A : Atom) :
    (Tensor.obj realD.data realC.data
      (Obj.singleton A) (Obj.singleton (rightDualAtom A))).atom
        (rightDualSlotIndex A) = (0, 0) := by
  rcases A with ⟨a, s⟩
  change Tensor.slotAtom realD.data realC.data
      (Obj.singleton (a, s)) (Obj.singleton (rightDualAtom (a, s)))
      ((slotsEquiv realD.data realC.data
        (Obj.singleton (a, s))
        (Obj.singleton (rightDualAtom (a, s))))
          ((slotsEquiv realD.data realC.data
            (Obj.singleton (a, s))
            (Obj.singleton (rightDualAtom (a, s)))).symm
              (rightDualSlot (a, s)))) = (0, 0)
  rw [Equiv.apply_symm_apply]
  change
    (a + -a,
      s + (s + shiftNu realComputableShiftData.cochains a (-a)) +
        realC.data.rowParity a (-a) (inverseEvenRow a)) = (0, 0)
  rw [inverseEvenRow_parity]
  apply Prod.ext
  · simp
  · simp only [add_assoc, zmod2_add_self, add_zero]

/-! ## The split coevaluation coordinate -/

/-- Inclusion of a coordinate whose complete atom has been identified with
`B`.  Keeping the equality explicit makes the dependent atom transport
available to the accompanying laws. -/
private def coordinateInclusion (X : Obj) (i : Fin X.size) (B : Atom)
    (h : X.atom i = B) : Hom realD.data (Obj.singleton B) X := by
  subst B
  exact Finite.atomInclusion X i

/-- Projection paired with `coordinateInclusion`. -/
private def coordinateProjection (X : Obj) (i : Fin X.size) (B : Atom)
    (h : X.atom i = B) : Hom realD.data X (Obj.singleton B) := by
  subst B
  exact Finite.atomProjection X i

private theorem coordinateInclusion_even (X : Obj) (i : Fin X.size)
    (B : Atom) (h : X.atom i = B) :
    Hom.MemGrade 0 (coordinateInclusion X i B h) := by
  subst B
  exact Finite.atomInclusion_even realD.laws X i

private theorem coordinateProjection_even (X : Obj) (i : Fin X.size)
    (B : Atom) (h : X.atom i = B) :
    Hom.MemGrade 0 (coordinateProjection X i B h) := by
  subst B
  exact Finite.atomProjection_even realD.laws X i

private theorem coordinateInclusion_projection (X : Obj) (i : Fin X.size)
    (B : Atom) (h : X.atom i = B) :
    Hom.comp (coordinateInclusion X i B h)
        (coordinateProjection X i B h) =
      Hom.id realD.data (Obj.singleton B) := by
  subst B
  exact Finite.atomInclusion_projection_self realD.laws X i

/-- Inclusion of the distinguished unit atom into the forward tensor. -/
def rightCoevaluation (A : Atom) :
    Hom realD.data (Obj.singleton (0, 0))
      (Tensor.obj realD.data realC.data
        (Obj.singleton A) (Obj.singleton (rightDualAtom A))) := by
  exact coordinateInclusion _ (rightDualSlotIndex A) (0, 0)
    (rightDualSlot_atom A)

/-- Projection back from the distinguished unit coordinate. -/
def rightCoevaluationProjection (A : Atom) :
    Hom realD.data
      (Tensor.obj realD.data realC.data
        (Obj.singleton A) (Obj.singleton (rightDualAtom A)))
      (Obj.singleton (0, 0)) := by
  exact coordinateProjection _ (rightDualSlotIndex A) (0, 0)
    (rightDualSlot_atom A)

/-- The chosen coevaluation coordinate is even. -/
theorem rightCoevaluation_even (A : Atom) :
    Hom.MemGrade 0 (rightCoevaluation A) := by
  exact coordinateInclusion_even _ _ _ (rightDualSlot_atom A)

/-- Its coordinate projection is even. -/
theorem rightCoevaluationProjection_even (A : Atom) :
    Hom.MemGrade 0 (rightCoevaluationProjection A) := by
  exact coordinateProjection_even _ _ _ (rightDualSlot_atom A)

/-- The coordinate inclusion is split by the matching projection. -/
theorem rightCoevaluation_split (A : Atom) :
    Hom.comp (rightCoevaluation A) (rightCoevaluationProjection A) =
      Hom.id realD.data (Obj.singleton (0, 0)) := by
  exact coordinateInclusion_projection _ _ _ (rightDualSlot_atom A)

/-! ## Homogeneous comparisons between singleton shifts -/

/-- The coefficient-one map between two shifts of the same label. -/
def atomShiftHom (a : ZMod 8) (s t : ZMod 2) :
    AtomHom realD.data (a, s) (a, t) :=
  AtomHom.ofLabelEq rfl (realD.data.algebra a).one

private theorem paired_shift_degree (s t : ZMod 2) :
    (s + t) + s + t = 0 := by
  calc
    (s + t) + s + t = (s + s) + (t + t) := by abel
    _ = 0 := by rw [zmod2_add_self, zmod2_add_self, zero_add]

/-- The coefficient-one comparison has the sum of the endpoint shifts as
its categorical degree. -/
theorem atomShiftHom_mem (a : ZMod 8) (s t : ZMod 2) :
    AtomHom.MemGrade (s + t) (atomShiftHom a s t) := by
  intro h
  have hh : h =
      (rfl : Atom.label (a, s) = Atom.label (a, t)) :=
    Subsingleton.elim _ _
  rw [hh]
  change (realD.data.algebra a).MemGrade ((s + t) + s + t)
    ((atomShiftHom a s t).coeff rfl)
  rw [atomShiftHom, AtomHom.coeff_ofLabelEq]
  rw [paired_shift_degree]
  exact (DLaws.algebra_laws realD.laws a).one_mem

/-- Reversing a coefficient-one shift comparison gives its inverse. -/
theorem atomShiftHom_comp (a : ZMod 8) (s t : ZMod 2) :
    AtomHom.comp (atomShiftHom a s t) (atomShiftHom a t s) =
      AtomHom.id realD.data (a, s) := by
  apply AtomHom.ext_same_label
  simp only [AtomHom.coeff_comp_same_label, atomShiftHom,
    AtomHom.coeff_ofLabelEq, AtomHom.coeff_id]
  exact (DLaws.algebra_laws realD.laws a).one_mul
    (realD.data.algebra a).one

/-- The singleton matrix supported by `atomShiftHom`. -/
def singletonShiftHom (a : ZMod 8) (s t : ZMod 2) :
    Hom realD.data (Obj.singleton (a, s)) (Obj.singleton (a, t)) :=
  fun _ _ => atomShiftHom a s t

theorem singletonShiftHom_mem (a : ZMod 8) (s t : ZMod 2) :
    Hom.MemGrade (s + t) (singletonShiftHom a s t) := by
  intro _ _
  exact atomShiftHom_mem a s t

theorem singletonShiftHom_comp (a : ZMod 8) (s t : ZMod 2) :
    Hom.comp (singletonShiftHom a s t) (singletonShiftHom a t s) =
      Hom.id realD.data (Obj.singleton (a, s)) := by
  apply Hom.ext
  intro i j
  have hi := Finite.eq_singletonIndex (a, s) i
  have hj := Finite.eq_singletonIndex (a, s) j
  subst i
  subst j
  rw [Hom.comp, AtomHom.finSum_eq_sum]
  rw [Fintype.sum_eq_single (Finite.singletonIndex (a, t))]
  · change AtomHom.comp (atomShiftHom a s t) (atomShiftHom a t s) =
      AtomHom.id realD.data (a, s)
    exact atomShiftHom_comp a s t
  · intro k hk
    exact (hk (Finite.eq_singletonIndex (a, t) k)).elim

/-- Any two singleton atoms with the same label are homogeneously
isomorphic; their degree is the sum of their shifts. -/
def singletonSameLabelIso (A B : Atom) (h : A.label = B.label) :
    Superfusion.Category.HomogeneousIso ℝ (A.shift + B.shift)
      (Obj.singleton A) (Obj.singleton B) := by
  rcases A with ⟨a, s⟩
  rcases B with ⟨b, t⟩
  change a = b at h
  subst b
  exact
    { iso :=
        { hom := singletonShiftHom a s t
          inv := singletonShiftHom a t s
          hom_inv_id := singletonShiftHom_comp a s t
          inv_hom_id := singletonShiftHom_comp a t s }
      hom_mem := singletonShiftHom_mem a s t
      inv_mem := by
        change Hom.MemGrade (s + t) (singletonShiftHom a t s)
        simpa only [add_comm] using singletonShiftHom_mem a t s }

/-- Graded Schur for the Mathlib view of two concrete singleton atoms. -/
theorem singleton_isIso_of_homogeneous_of_ne_zero
    (A B : Atom) (d : ZMod 2)
    (f : Obj.singleton A ⟶ Obj.singleton B)
    (hf : f ∈ Superfusion.Category.homGrade ℝ
      (Obj.singleton A) (Obj.singleton B) d)
    (hf0 : f ≠ 0) : IsIso f := by
  change Hom realD.data (Obj.singleton A) (Obj.singleton B) at f
  change Hom.MemGrade d f at hf
  change f ≠ Hom.zero realD.data (Obj.singleton A) (Obj.singleton B) at hf0
  obtain ⟨g, hfg, hgf⟩ := RealSemisimple.graded_schur_raw
    (RealSemisimple.singleton_simple A)
    (RealSemisimple.singleton_simple B) f hf hf0
  exact ⟨⟨g, hfg, hgf⟩⟩

/-! ## Even biproduct decomposition of a coordinate tuple -/

/-- The listed atoms of `X`, with the raw coordinate inclusions and
projections, form an even bicone whose point is `X` itself. -/
noncomputable def atomBicone (X : Obj) :
    Limits.Bicone (fun i : Fin X.size =>
      Superfusion.Category.evenObj ℝ Obj (Obj.singleton (X.atom i))) where
  pt := Superfusion.Category.evenObj ℝ Obj X
  π := fun i =>
    ⟨Finite.atomProjection (dD := realD.data) X i,
      Finite.atomProjection_even realD.laws X i⟩
  ι := fun i =>
    ⟨Finite.atomInclusion (dD := realD.data) X i,
      Finite.atomInclusion_even realD.laws X i⟩
  ι_π := by
    intro i j
    by_cases hij : i = j
    · subst j
      apply WideSubcategory.hom_ext
      simp only
      change
        Hom.comp (Finite.atomInclusion (dD := realD.data) X i)
            (Finite.atomProjection (dD := realD.data) X i) =
          Hom.id realD.data (Obj.singleton (X.atom i))
      exact Finite.atomInclusion_projection_self realD.laws X i
    · apply WideSubcategory.hom_ext
      simp only [dif_neg hij]
      exact Finite.atomInclusion_projection_ne realD.laws X i j hij

/-- The coordinate projections and inclusions resolve the identity of `X`
in the even subcategory. -/
theorem atomBicone_total (X : Obj) :
    ∑ i, (atomBicone X).π i ≫ (atomBicone X).ι i =
      𝟙 (atomBicone X).pt := by
  apply WideSubcategory.hom_ext
  have htotal := Finite.atomProjection_inclusion_total
    realComputableShiftedRawDCT.data realUnitRowsData X
  rw [Finite.candidateFinSum_eq_sum
    realComputableShiftedRawDCT.data realUnitRowsData] at htotal
  let P := Superfusion.Category.evenMorphismProperty ℝ Obj
  let F := wideSubcategoryInclusion P
  change
    F.map (∑ i, (atomBicone X).π i ≫ (atomBicone X).ι i) =
      F.map (𝟙 (atomBicone X).pt)
  rw [Functor.map_sum, F.map_id]
  simp_rw [F.map_comp]
  change
    (∑ i, Hom.comp
        (Finite.atomProjection (dD := realD.data) X i)
        (Finite.atomInclusion (dD := realD.data) X i)) =
      Hom.id realD.data X
  exact htotal

/-- The concrete coordinate tuple is the Mathlib finite biproduct of its
listed singleton atoms. -/
noncomputable def atomDecompositionIso (X : Obj) :
    Superfusion.Category.evenObj ℝ Obj X ≅
      ⨁ fun i : Fin X.size =>
        Superfusion.Category.evenObj ℝ Obj
          (Obj.singleton (X.atom i)) :=
  biproduct.uniqueUpToIso _
    (Limits.isBilimitOfTotal (atomBicone X) (atomBicone_total X))

/-! ## Supermultiplicity of the reversed inverse-label tensor -/

/-- The reversed tensor needed as the evaluation domain. -/
def reverseTensor (A : Atom) : Obj :=
  Tensor.obj realD.data realC.data
    (Obj.singleton (rightDualAtom A)) (Obj.singleton A)

/-- Every atom of the reversed inverse-label tensor has neutral label. -/
theorem reverseTensor_atom_label (A : Atom)
    (i : Fin (reverseTensor A).size) :
    Atom.label ((reverseTensor A).atom i) = 0 := by
  change Atom.label
    (Tensor.slotAtom realD.data realC.data
      (Obj.singleton (rightDualAtom A)) (Obj.singleton A)
      ((Tensor.slots realD.data realC.data
        (Obj.singleton (rightDualAtom A)) (Obj.singleton A)).get i)) = 0
  change
    Atom.label ((Obj.singleton (rightDualAtom A)).atom _) +
      Atom.label ((Obj.singleton A).atom _) = 0
  rw [Finite.singleton_atom, Finite.singleton_atom]
  rcases A with ⟨a, s⟩
  change -a + a = 0
  simp

/-- Sort the listed reversed-tensor atoms by their stored shifts. -/
noncomputable def reverseTensorSort (A : Atom) :=
  Superfusion.Category.superIndexSort
    (fun i : Fin (reverseTensor A).size =>
      (reverseTensor A).atom i |>.shift)

/-- Each sorted neutral singleton is the prescribed homogeneous copy of
the unshifted tensor unit. -/
noncomputable def reverseTensorSummandIso (A : Atom)
    (i : Superfusion.Category.SuperIndex
      (reverseTensorSort A).evenMultiplicity
      (reverseTensorSort A).oddMultiplicity) :
    Superfusion.Category.HomogeneousIso ℝ
      (Superfusion.Category.superIndexParity i)
      (Obj.singleton
        ((reverseTensor A).atom ((reverseTensorSort A).equiv i)))
      (Obj.singleton (0, 0)) := by
  let B := (reverseTensor A).atom ((reverseTensorSort A).equiv i)
  have hB : B.label = (0 : ZMod 8) :=
    reverseTensor_atom_label A ((reverseTensorSort A).equiv i)
  have hLabel : B.label = Atom.label (0, 0) := by
    change B.label = 0
    exact hB
  let e := singletonSameLabelIso B (0, 0) hLabel
  rw [← (reverseTensorSort A).parity i]
  simpa only [B, Atom.shift, add_zero] using e

/-- The full reversed tensor is a parity-sorted finite sum of homogeneous
copies of the unit. -/
noncomputable def reverseTensorMultiplicity (A : Atom) :
    Superfusion.Category.SuperMultiplicityWitness ℝ Obj
      (reverseTensor A) (Obj.singleton (0, 0))
      (reverseTensorSort A).evenMultiplicity
      (reverseTensorSort A).oddMultiplicity where
  summand := fun i =>
    Obj.singleton
      ((reverseTensor A).atom ((reverseTensorSort A).equiv i))
  summandIso := reverseTensorSummandIso A
  decomposition :=
    (atomDecompositionIso (reverseTensor A)).trans
      ((reverseTensorSort A).biproductReindex
        (fun i : Fin (reverseTensor A).size =>
          Superfusion.Category.evenObj ℝ Obj
            (Obj.singleton ((reverseTensor A).atom i))))

/-! ### Positivity -/

/-- One explicit row of the reversed tensor; it is used only to witness
that the sorted multiplicity is not empty. -/
def reverseTensorSlot (A : Atom) :
    Tensor.Slot realD.data realC.data
      (Obj.singleton (rightDualAtom A)) (Obj.singleton A) :=
  ⟨Finite.singletonIndex (rightDualAtom A),
    Finite.singletonIndex A, by
      simpa only [Finite.singleton_atom, rightDualAtom, Atom.label,
        neg_neg] using inverseEvenRow (-A.label)⟩

/-- The explicit reversed-tensor row in the canonical slot enumeration. -/
def reverseTensorSlotIndex (A : Atom) : Fin (reverseTensor A).size :=
  (slotsEquiv realD.data realC.data
    (Obj.singleton (rightDualAtom A)) (Obj.singleton A)).symm
      (reverseTensorSlot A)

/-- The reversed tensor has at least one coordinate. -/
theorem reverseTensor_size_pos (A : Atom) : 0 < (reverseTensor A).size := by
  have h := (reverseTensorSlotIndex A).isLt
  omega

/-- Consequently its even and odd unit multiplicities have positive total. -/
theorem reverseTensorMultiplicity_pos (A : Atom) :
    0 < (reverseTensorSort A).evenMultiplicity +
      (reverseTensorSort A).oddMultiplicity := by
  rw [(reverseTensorSort A).total_eq]
  exact reverseTensor_size_pos A

/-! ## Supermultiplicity of the forward inverse-label tensor -/

/-- The forward tensor used by the final weak-invertibility witness. -/
def forwardTensor (A : Atom) : Obj :=
  Tensor.obj realD.data realC.data
    (Obj.singleton A) (Obj.singleton (rightDualAtom A))

/-- Every atom of the forward inverse-label tensor has neutral label. -/
theorem forwardTensor_atom_label (A : Atom)
    (i : Fin (forwardTensor A).size) :
    Atom.label ((forwardTensor A).atom i) = 0 := by
  change Atom.label
    (Tensor.slotAtom realD.data realC.data
      (Obj.singleton A) (Obj.singleton (rightDualAtom A))
      ((Tensor.slots realD.data realC.data
        (Obj.singleton A) (Obj.singleton (rightDualAtom A))).get i)) = 0
  change
    Atom.label ((Obj.singleton A).atom _) +
      Atom.label ((Obj.singleton (rightDualAtom A)).atom _) = 0
  rw [Finite.singleton_atom, Finite.singleton_atom]
  rcases A with ⟨a, s⟩
  change a + -a = 0
  simp

/-- Sort the forward tensor coordinates by parity. -/
noncomputable def forwardTensorSort (A : Atom) :=
  Superfusion.Category.superIndexSort
    (fun i : Fin (forwardTensor A).size =>
      Atom.shift ((forwardTensor A).atom i))

/-- The sorted forward summands are homogeneous unit copies. -/
noncomputable def forwardTensorSummandIso (A : Atom)
    (i : Superfusion.Category.SuperIndex
      (forwardTensorSort A).evenMultiplicity
      (forwardTensorSort A).oddMultiplicity) :
    Superfusion.Category.HomogeneousIso ℝ
      (Superfusion.Category.superIndexParity i)
      (Obj.singleton
        ((forwardTensor A).atom ((forwardTensorSort A).equiv i)))
      (Obj.singleton (0, 0)) := by
  let B := (forwardTensor A).atom ((forwardTensorSort A).equiv i)
  have hB : B.label = (0 : ZMod 8) :=
    forwardTensor_atom_label A ((forwardTensorSort A).equiv i)
  have hLabel : B.label = Atom.label (0, 0) := by
    change B.label = 0
    exact hB
  let e := singletonSameLabelIso B (0, 0) hLabel
  rw [← (forwardTensorSort A).parity i]
  simpa only [B, Atom.shift, add_zero] using e

/-- Full forward supermultiplicity by parity-sorting every coordinate. -/
noncomputable def forwardTensorMultiplicity (A : Atom) :
    Superfusion.Category.SuperMultiplicityWitness ℝ Obj
      (forwardTensor A) (Obj.singleton (0, 0))
      (forwardTensorSort A).evenMultiplicity
      (forwardTensorSort A).oddMultiplicity where
  summand := fun i =>
    Obj.singleton
      ((forwardTensor A).atom ((forwardTensorSort A).equiv i))
  summandIso := forwardTensorSummandIso A
  decomposition :=
    (atomDecompositionIso (forwardTensor A)).trans
      ((forwardTensorSort A).biproductReindex
        (fun i : Fin (forwardTensor A).size =>
          Superfusion.Category.evenObj ℝ Obj
            (Obj.singleton ((forwardTensor A).atom i))))

/-- The distinguished coevaluation slot proves the forward tensor nonempty. -/
theorem forwardTensor_size_pos (A : Atom) : 0 < (forwardTensor A).size := by
  change 0 < (Tensor.obj realD.data realC.data
    (Obj.singleton A) (Obj.singleton (rightDualAtom A))).size
  have h := (rightDualSlotIndex A).isLt
  exact lt_of_le_of_lt (Nat.zero_le _) h

/-- The forward unit supermultiplicity has positive total. -/
theorem forwardTensorMultiplicity_pos (A : Atom) :
    0 < (forwardTensorSort A).evenMultiplicity +
      (forwardTensorSort A).oddMultiplicity := by
  rw [(forwardTensorSort A).total_eq]
  exact forwardTensor_size_pos A

/-! ## Dual objects of arbitrary coordinate tuples -/

/-- The finite biproduct of the chosen right duals of all listed atoms. -/
noncomputable def rightDualObject (X : Obj) : Obj :=
  Superfusion.Category.superBiproduct (K := ℝ)
    (fun i : Fin X.size => Obj.singleton (rightDualAtom (X.atom i)))

/-- The finite biproduct of the chosen left duals of all listed atoms. -/
noncomputable def leftDualObject (X : Obj) : Obj :=
  Superfusion.Category.superBiproduct (K := ℝ)
    (fun i : Fin X.size => Obj.singleton (leftDualAtom (X.atom i)))

/-! ## Monoidal completion and exact right pairings -/

/-- Bundle any completed proof of the canonical real associator laws. -/
def realAssociator
    (hAssociator : AssociatorLaws
      realD.data realD.laws realTensor.data realTensor.laws
      (Associator.canonicalData realComputableShiftedRawDCT.data)) :
    Associator realD realTensor where
  data := Associator.canonicalData realComputableShiftedRawDCT.data
  laws := hAssociator

/-- Bundle any completed proof of the canonical real unitor laws. -/
def realUnitor
    (hAssociator : AssociatorLaws
      realD.data realD.laws realTensor.data realTensor.laws
      (Associator.canonicalData realComputableShiftedRawDCT.data))
    (hUnitor : UnitorLaws
      realD.data realD.laws realTensor.data realTensor.laws
      (realAssociator hAssociator).data (realAssociator hAssociator).laws
      (Unitor.canonicalData realComputableShiftedRawDCT.data
        realUnitRowsData)) :
    Unitor realD realTensor (realAssociator hAssociator) where
  data := Unitor.canonicalData realComputableShiftedRawDCT.data
    realUnitRowsData
  laws := hUnitor

section MonoidalPairing

variable (hAssociator : AssociatorLaws
  realD.data realD.laws realTensor.data realTensor.laws
  (Associator.canonicalData realComputableShiftedRawDCT.data))

variable (hUnitor : UnitorLaws
  realD.data realD.laws realTensor.data realTensor.laws
  (realAssociator hAssociator).data (realAssociator hAssociator).laws
  (Unitor.canonicalData realComputableShiftedRawDCT.data realUnitRowsData))

/-- Every shifted real singleton atom has an exact pairing with the
explicit inverse-label atom `rightDualAtom A`.

The evaluation is selected from the full reversed-tensor multiplicity by
coordinate detection.  Its nonzero snake is inverted by graded Schur and
then absorbed into the evaluation, so no matrix of associator entries is
recomputed here. -/
theorem singletonRightPairing_nonempty (A : Atom) :
    Nonempty
      (PairingAdapter.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        hAssociator hUnitor
        (Obj.singleton A) (Obj.singleton (rightDualAtom A))) := by
  classical
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  let X := Obj.singleton A
  let Y := Obj.singleton (rightDualAtom A)
  let η : 𝟙_ Obj ⟶ X ⊗ Y := rightCoevaluation A
  let π : X ⊗ Y ⟶ 𝟙_ Obj := rightCoevaluationProjection A
  have hη : η ∈ Superfusion.Category.homGrade ℝ (𝟙_ Obj) (X ⊗ Y) 0 := by
    change Hom.MemGrade 0 (rightCoevaluation A)
    exact rightCoevaluation_even A
  have hsplit : η ≫ π = 𝟙 (𝟙_ Obj) := by
    change Hom.comp (rightCoevaluation A) (rightCoevaluationProjection A) =
      Hom.id realD.data (Obj.singleton (0, 0))
    exact rightCoevaluation_split A
  let m : Superfusion.Category.SuperMultiplicityWitness ℝ Obj
      (Y ⊗ X) (𝟙_ Obj)
      (reverseTensorSort A).evenMultiplicity
      (reverseTensorSort A).oddMultiplicity :=
    reverseTensorMultiplicity A
  have hX : 𝟙 X ≠ 0 := by
    change Hom.id realD.data (Obj.singleton A) ≠
      Hom.zero realD.data (Obj.singleton A) (Obj.singleton A)
    exact RealSemisimple.singleton_id_ne_zero A
  obtain ⟨i, hi⟩ :=
    Superfusion.Category.exists_normalizedXSnake_projection_ne_zero
      η π hη hsplit m hX
  let ε := m.projection i
  have hε : ε ∈ Superfusion.Category.homGrade ℝ
      (Y ⊗ X) (𝟙_ Obj)
      (Superfusion.Category.superIndexParity i) :=
    m.projection_mem i
  let r := Superfusion.Category.normalizedXSnake η ε
  have hr : r ∈ Superfusion.Category.homGrade ℝ X X
      (Superfusion.Category.superIndexParity i) := by
    simpa only [zero_add] using
      Superfusion.Category.normalizedXSnake_mem η ε hη hε
  letI : IsIso r :=
    singleton_isIso_of_homogeneous_of_ne_zero A A
      (Superfusion.Category.superIndexParity i) r hr hi
  let ε₀ := Superfusion.Category.normalizeEvaluationByXSnake η ε
  have hε₀ : ε₀ ∈ Superfusion.Category.homGrade ℝ
      (Y ⊗ X) (𝟙_ Obj) 0 :=
    Superfusion.Category.normalizeEvaluationByXSnake_mem_even
      η ε hη hε
  have hsnake :
      Superfusion.Category.normalizedXSnake η ε₀ = 𝟙 X :=
    Superfusion.Category.normalizedXSnake_normalizeEvaluationByXSnake
      η ε hη hε
  let p : Superfusion.Category.SuperExactPairing ℝ X Y :=
    Superfusion.Category.SuperExactPairing.ofNormalizedXSnakeOfEvenSchur
      η ε₀ hη hε₀ hsnake hX (by
        intro g hg hg0
        exact singleton_isIso_of_homogeneous_of_ne_zero
          (rightDualAtom A) (rightDualAtom A) 0 g hg hg0)
  exact ⟨p⟩

/-- Category-level weak-invertibility data for one singleton atom. -/
noncomputable def singletonRightWeakInvertibilityWitness (A : Atom) :
    PairingAdapter.CategoryWeakInvertibilityWitness
      realComputableShiftedRawDCT.data
      realComputableShiftedRawDCT.laws realUnitRowsData
      hAssociator hUnitor (Obj.singleton A) := by
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  let w : Superfusion.Category.WeakInvertibilityWitness ℝ Obj
      (Obj.singleton A) :=
    { dual := Obj.singleton (rightDualAtom A)
      pairing := Classical.choice
        (singletonRightPairing_nonempty hAssociator hUnitor A)
      evenMultiplicity := (forwardTensorSort A).evenMultiplicity
      oddMultiplicity := (forwardTensorSort A).oddMultiplicity
      multiplicity_pos := forwardTensorMultiplicity_pos A
      multiplicity := forwardTensorMultiplicity A }
  exact w

/-- The same singleton weak-invertibility witness at the raw candidate
boundary. -/
noncomputable def rawSingletonRightWeakInvertibilityWitness (A : Atom) :
    realCandidateData.WeakInvertibilityWitness (Obj.singleton A) :=
  PairingAdapter.weakInvertibilityWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData hAssociator hUnitor
    (singletonRightWeakInvertibilityWitness hAssociator hUnitor A)

/-! ## Left atomic pairings from the same inverse-label construction -/

/-- The right pairing applied to `leftDualAtom A` is a left pairing for
`A`, because its displayed right dual reduces to `A`. -/
theorem singletonLeftPairing_nonempty (A : Atom) :
    Nonempty
      (PairingAdapter.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        hAssociator hUnitor
        (Obj.singleton (leftDualAtom A)) (Obj.singleton A)) := by
  simpa only [rightDual_leftDual] using
    singletonRightPairing_nonempty hAssociator hUnitor (leftDualAtom A)

/-! ## Pairings for arbitrary finite coordinate tuples -/

/-- Componentwise right pairings extend across the canonical finite atom
decomposition of every coordinate tuple. -/
theorem objectRightPairing_nonempty (X : Obj) :
    Nonempty
      (PairingAdapter.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        hAssociator hUnitor X (rightDualObject X)) := by
  classical
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) :=
    MathlibAdapter.evenHasFiniteBiproducts
      realComputableShiftedRawDCT.data realD.laws realUnitRowsData
  let e := Superfusion.Category.evenIsoOfEvenSubcategoryIso
    (atomDecompositionIso X)
  let atomPairing (i : Fin X.size) :
      Superfusion.Category.SuperExactPairing ℝ
        (Obj.singleton (X.atom i))
        (Obj.singleton (rightDualAtom (X.atom i))) :=
    Classical.choice
      (singletonRightPairing_nonempty hAssociator hUnitor (X.atom i))
  let p := Superfusion.Category.SuperExactPairing.biproduct
    atomPairing
  let q : Superfusion.Category.SuperExactPairing ℝ
      X (rightDualObject X) :=
    Superfusion.Category.SuperExactPairing.congrLeft e p
  exact ⟨q⟩

/-- Componentwise left pairings likewise extend across every finite atom
decomposition. -/
theorem objectLeftPairing_nonempty (X : Obj) :
    Nonempty
      (PairingAdapter.CategoryExactPairing
        realComputableShiftedRawDCT.data
        realComputableShiftedRawDCT.laws realUnitRowsData
        hAssociator hUnitor (leftDualObject X) X) := by
  classical
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : HasFiniteBiproducts
      (Superfusion.Category.EvenSubcategory ℝ Obj) :=
    MathlibAdapter.evenHasFiniteBiproducts
      realComputableShiftedRawDCT.data realD.laws realUnitRowsData
  let e := Superfusion.Category.evenIsoOfEvenSubcategoryIso
    (atomDecompositionIso X)
  let atomPairing (i : Fin X.size) :
      Superfusion.Category.SuperExactPairing ℝ
        (Obj.singleton (leftDualAtom (X.atom i)))
        (Obj.singleton (X.atom i)) :=
    Classical.choice
      (singletonLeftPairing_nonempty hAssociator hUnitor (X.atom i))
  let p := Superfusion.Category.SuperExactPairing.biproduct
    atomPairing
  let q : Superfusion.Category.SuperExactPairing ℝ
      (leftDualObject X) X :=
    Superfusion.Category.SuperExactPairing.congrRight e p
  exact ⟨q⟩

/-! ## Raw candidate boundary -/

include hAssociator hUnitor

/-- Every raw coordinate object has a right exact-pairing witness. -/
theorem raw_has_right_dual (X : Obj) :
    ∃ Y : Obj, Nonempty (realCandidateData.ExactPairingWitness X Y) := by
  refine ⟨rightDualObject X, ?_⟩
  obtain ⟨p⟩ := objectRightPairing_nonempty hAssociator hUnitor X
  exact ⟨PairingAdapter.exactPairingWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData hAssociator hUnitor p⟩

/-- Every raw coordinate object has a left exact-pairing witness. -/
theorem raw_has_left_dual (X : Obj) :
    ∃ Y : Obj, Nonempty (realCandidateData.ExactPairingWitness Y X) := by
  refine ⟨leftDualObject X, ?_⟩
  obtain ⟨p⟩ := objectLeftPairing_nonempty hAssociator hUnitor X
  exact ⟨PairingAdapter.exactPairingWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData hAssociator hUnitor p⟩

/-- Every simple raw coordinate object is weakly invertible. -/
theorem raw_weaklyPointed (X : Obj)
    (hX : realCandidateData.IsSimple X) :
    realCandidateData.IsWeaklyInvertible X := by
  classical
  obtain ⟨i, ⟨e⟩⟩ := RealSemisimple.simple_iso_atom hX
  letI : MonoidalCategoryStruct Obj :=
    MathlibAdapter.monoidalCategoryStruct realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  letI : Superfusion.Category.MonoidalSupercategory ℝ Obj :=
    MathlibAdapter.monoidalSupercategory realD realTensor
      (realAssociator hAssociator) (realUnitor hAssociator hUnitor)
  let e' := PairingAdapter.homogeneousIso
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws) realUnitRowsData e
  let w : Superfusion.Category.WeakInvertibilityWitness ℝ Obj X :=
    Superfusion.Category.WeakInvertibilityWitness.congrLeft e'
      (singletonRightWeakInvertibilityWitness
        hAssociator hUnitor (X.atom i))
  exact ⟨PairingAdapter.weakInvertibilityWitness
    (x := realComputableShiftedRawDCT.data)
    (hx := realComputableShiftedRawDCT.laws)
    realUnitRowsData hAssociator hUnitor w⟩

end MonoidalPairing

/-! ## Closed nontrivial dual evaluations -/

example : rightDualAtom (1, 0) = (7, 1) := rfl

example : leftDualAtom (3, 1) = (5, 0) := rfl

end RealPairing

end Superfusion.RMod.FromRawDCT
