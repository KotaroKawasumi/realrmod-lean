import Mathlib.Algebra.BigOperators.Fin
import Superfusion.RMod.FromRawDCT.Candidate
import Superfusion.WeaklyPointedSuperfusion.CandidateLaws

/-!
# Finite additive witnesses for raw-DCT coordinate envelopes

This abstract proof layer constructs canonical finite biproducts and the
decomposition of every coordinate object into its listed singleton atoms.
The executable candidate data are not changed: the auxiliary additive and
module instances below are available only when exact `DLaws` are supplied
through `Fact`.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT
open CandidateData

/-! ## Proof-layer additive structures -/

instance atomHomZero {dD : DData} [Fact (DLaws dD)] {X Y : Atom} :
    Zero (AtomHom dD X Y) :=
  ⟨AtomHom.zero dD X Y⟩

instance atomHomAdd {dD : DData} [Fact (DLaws dD)] {X Y : Atom} :
    Add (AtomHom dD X Y) :=
  ⟨AtomHom.add⟩

instance atomHomNeg {dD : DData} [Fact (DLaws dD)] {X Y : Atom} :
    Neg (AtomHom dD X Y) :=
  ⟨AtomHom.neg⟩

instance atomHomSub {dD : DData} [Fact (DLaws dD)] {X Y : Atom} :
    Sub (AtomHom dD X Y) :=
  ⟨fun f g => AtomHom.add f (AtomHom.neg g)⟩

instance atomHomSMul {dD : DData} [Fact (DLaws dD)] {X Y : Atom} :
    SMul ℝ (AtomHom dD X Y) :=
  ⟨AtomHom.smul⟩

instance atomHomAddCommGroup {dD : DData} [hD : Fact (DLaws dD)]
    {X Y : Atom} : AddCommGroup (AtomHom dD X Y) where
  add_assoc := AtomHom.add_assoc hD.out
  zero_add := AtomHom.zero_add hD.out
  add_zero := AtomHom.add_zero hD.out
  neg_add_cancel := AtomHom.neg_add hD.out
  add_comm := AtomHom.add_comm hD.out
  sub_eq_add_neg := fun _ _ => rfl
  nsmul := nsmulRec
  zsmul := zsmulRec

instance atomHomModule {dD : DData} [hD : Fact (DLaws dD)] {X Y : Atom} :
    Module ℝ (AtomHom dD X Y) where
  one_smul := AtomHom.one_smul hD.out
  mul_smul := AtomHom.mul_smul hD.out
  smul_add := AtomHom.smul_add hD.out
  smul_zero := AtomHom.smul_zero hD.out
  add_smul := AtomHom.add_smul hD.out
  zero_smul := AtomHom.zero_smul hD.out

namespace AtomHom

variable {dD : DData} [hD : Fact (DLaws dD)]

@[simp] theorem zero_eq {X Y : Atom} :
    (0 : AtomHom dD X Y) = zero dD X Y := rfl

@[simp] theorem add_eq {X Y : Atom} (f g : AtomHom dD X Y) :
    f + g = add f g := rfl

@[simp] theorem comp_zero_fact {X Y Z : Atom} (f : AtomHom dD X Y) :
    comp f (0 : AtomHom dD Y Z) = 0 :=
  comp_zero hD.out f

@[simp] theorem comp_explicit_zero {X Y Z : Atom} (f : AtomHom dD X Y) :
    comp f (zero dD Y Z) = zero dD X Z :=
  comp_zero hD.out f

@[simp] theorem zero_comp_fact {X Y Z : Atom} (g : AtomHom dD Y Z) :
    comp (0 : AtomHom dD X Y) g = 0 :=
  zero_comp hD.out g

@[simp] theorem explicit_zero_comp {X Y Z : Atom} (g : AtomHom dD Y Z) :
    comp (zero dD X Y) g = zero dD X Z :=
  zero_comp hD.out g

@[simp] theorem comp_id_fact {X Y : Atom} (f : AtomHom dD X Y) :
    comp f (id dD Y) = f :=
  comp_id hD.out f

@[simp] theorem comp_explicit_id {X Y : Atom} (f : AtomHom dD X Y) :
    comp f (id dD Y) = f :=
  comp_id hD.out f

@[simp] theorem id_comp_fact {X Y : Atom} (f : AtomHom dD X Y) :
    comp (id dD X) f = f :=
  id_comp hD.out f

@[simp] theorem explicit_id_comp {X Y : Atom} (f : AtomHom dD X Y) :
    comp (id dD X) f = f :=
  id_comp hD.out f

/-- The raw fixed-order sum agrees with the ordinary finite sum in the
proof-layer additive group. -/
theorem finSum_eq_sum {X Y : Atom} {n : ℕ}
    (f : Fin n → AtomHom dD X Y) :
    finSum n f = ∑ i, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [finSum, ih, Fin.sum_univ_castSucc]
      rfl

end AtomHom

namespace Finite

/-! ## Candidate finite sums -/

variable (x : RawDCTData) (rows : UnitRowsData x.D x.C)

@[simp] theorem singleton_atom (A : Atom) (i : Fin (Obj.singleton A).size) :
    (Obj.singleton A).atom i = A := by
  fin_cases i
  rfl

@[simp] theorem singleton_size (A : Atom) : (Obj.singleton A).size = 1 := by
  rfl

/-- The candidate's recursive sum is the ordinary pointwise matrix sum. -/
theorem candidateFinSum_eq_sum [Fact (DLaws x.D)] {X Y : Obj} (n : ℕ)
    (f : Fin n → Hom x.D X Y) :
    (Candidate.data x rows).finSum n f = ∑ i, f i := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [CandidateData.finSum, ih, Fin.sum_univ_castSucc]
      rfl

/-- The candidate's even/odd recursive sum is the ordinary sum over the
disjoint union of its two finite index sets. -/
theorem candidateSuperFinSum_eq_sum [Fact (DLaws x.D)] {X Y : Obj}
    {p q : ℕ} (f : Fin p ⊕ Fin q → Hom x.D X Y) :
    (Candidate.data x rows).superFinSum f = ∑ i, f i := by
  rw [CandidateData.superFinSum,
    candidateFinSum_eq_sum x rows, candidateFinSum_eq_sum x rows]
  exact (Fintype.sum_sum_type f).symm

/-! ## Canonical concatenation -/

/-- Total number of atoms in a finite family. -/
def totalSize {n : ℕ} (S : Fin n → Obj) : ℕ :=
  ∑ i, (S i).size

/-- Pack a family index and an atom index into the flattened tuple. -/
def pack {n : ℕ} (S : Fin n → Obj) :
    ((i : Fin n) × Fin (S i).size) ≃ Fin (totalSize S) :=
  finSigmaFinEquiv

/-- Flatten a finite family of coordinate objects in canonical order. -/
def sumObj {n : ℕ} (S : Fin n → Obj) : Obj :=
  ⟨totalSize S, fun q =>
    let p := (pack S).symm q
    (S p.1).atom p.2⟩

/-- A packed coordinate has the original atom. -/
@[simp] theorem sumObj_atom_pack {n : ℕ} (S : Fin n → Obj)
    (i : Fin n) (k : Fin (S i).size) :
    (sumObj S).atom (pack S ⟨i, k⟩) = (S i).atom k := by
  change (S ((pack S).symm (pack S ⟨i, k⟩)).1).atom
      ((pack S).symm (pack S ⟨i, k⟩)).2 = (S i).atom k
  rw [Equiv.symm_apply_apply]

/-- `pack` with its codomain displayed as the index type of `sumObj`. -/
def packIndex {n : ℕ} (S : Fin n → Obj) (i : Fin n)
    (k : Fin (S i).size) : Fin (sumObj S).size :=
  pack S ⟨i, k⟩

/-- The packing equivalence with its codomain displayed definitionally as
the index type of the flattened object. -/
def packObjEquiv {n : ℕ} (S : Fin n → Obj) :
    ((i : Fin n) × Fin (S i).size) ≃ Fin (sumObj S).size :=
  pack S

@[simp] theorem packObjEquiv_apply {n : ℕ} (S : Fin n → Obj)
    (i : Fin n) (k : Fin (S i).size) :
    packObjEquiv S ⟨i, k⟩ = packIndex S i k := rfl

@[simp] theorem sumObj_atom_packIndex {n : ℕ} (S : Fin n → Obj)
    (i : Fin n) (k : Fin (S i).size) :
    (sumObj S).atom (packIndex S i k) = (S i).atom k :=
  sumObj_atom_pack S i k

/-- Identity transport along equality of complete atoms. -/
def atomEqHom {dD : DData} {X Y : Atom} (h : X = Y) : AtomHom dD X Y := by
  subst Y
  exact AtomHom.id dD X

theorem atomEqHom_even {dD : DData} (hD : DLaws dD)
    {X Y : Atom} (h : X = Y) :
    AtomHom.MemGrade 0 (atomEqHom (dD := dD) h) := by
  subst Y
  exact AtomHom.id_even hD X

@[simp] theorem atomEqHom_comp_symm {dD : DData} (hD : DLaws dD)
    {X Y : Atom} (h : X = Y) :
    AtomHom.comp (atomEqHom (dD := dD) h) (atomEqHom h.symm) =
      AtomHom.id dD X := by
  subst Y
  exact AtomHom.comp_id hD (AtomHom.id dD X)

/-! ## Family inclusions and projections -/

/-- Inclusion of one family member into its flattened sum. -/
def familyInclusion {dD : DData} {n : ℕ} (S : Fin n → Obj) (i : Fin n) :
    Hom dD (S i) (sumObj S) := fun k q =>
  if hq : q = packIndex S i k then by
    subst q
    exact atomEqHom (sumObj_atom_packIndex S i k).symm
  else AtomHom.zero dD _ _

/-- Projection from the flattened sum onto one family member. -/
def familyProjection {dD : DData} {n : ℕ} (S : Fin n → Obj) (i : Fin n) :
    Hom dD (sumObj S) (S i) := fun q k =>
  if hq : q = packIndex S i k then by
    subst q
    exact atomEqHom (sumObj_atom_packIndex S i k)
  else AtomHom.zero dD _ _

theorem familyInclusion_even {dD : DData} (hD : DLaws dD)
    {n : ℕ} (S : Fin n → Obj) (i : Fin n) :
    Hom.MemGrade 0 (familyInclusion (dD := dD) S i) := by
  intro k q
  by_cases hq : q = packIndex S i k
  · subst q
    simpa [familyInclusion] using
      atomEqHom_even hD (sumObj_atom_packIndex S i k).symm
  · simp [familyInclusion, hq]
    exact AtomHom.zero_memGrade hD 0

theorem familyProjection_even {dD : DData} (hD : DLaws dD)
    {n : ℕ} (S : Fin n → Obj) (i : Fin n) :
    Hom.MemGrade 0 (familyProjection (dD := dD) S i) := by
  intro q k
  by_cases hq : q = packIndex S i k
  · subst q
    simpa [familyProjection] using
      atomEqHom_even hD (sumObj_atom_packIndex S i k)
  · simp [familyProjection, hq]
    exact AtomHom.zero_memGrade hD 0

theorem familyInclusion_projection_self {dD : DData} (hD : DLaws dD)
    {n : ℕ} (S : Fin n → Obj) (i : Fin n) :
    Hom.comp (familyInclusion (dD := dD) S i) (familyProjection S i) =
      Hom.id dD (S i) := by
  classical
  letI : Fact (DLaws dD) := ⟨hD⟩
  funext k l
  rw [Hom.comp, AtomHom.finSum_eq_sum]
  by_cases hkl : k = l
  · subst l
    calc
      (∑ q, AtomHom.comp (familyInclusion S i k q)
          (familyProjection S i q k)) =
          AtomHom.comp
            (familyInclusion S i k (packIndex S i k))
            (familyProjection S i (packIndex S i k) k) :=
        Fintype.sum_eq_single _ (by
          intro q hq
          rw [familyInclusion, dif_neg hq]
          exact AtomHom.zero_comp hD _)
      _ = Hom.id dD (S i) k k := by
        simp [familyInclusion, familyProjection, Hom.id,
          atomEqHom_comp_symm hD]
  · have hpack : packIndex S i k ≠ packIndex S i l := by
      intro hp
      have hs : (⟨i, k⟩ : (i : Fin n) × Fin (S i).size) = ⟨i, l⟩ :=
        (pack S).injective hp
      cases hs
      exact hkl rfl
    calc
      (∑ q, AtomHom.comp (familyInclusion S i k q)
          (familyProjection S i q l)) =
          AtomHom.comp
            (familyInclusion S i k (packIndex S i k))
            (familyProjection S i (packIndex S i k) l) :=
        Fintype.sum_eq_single _ (by
          intro q hq
          rw [familyInclusion, dif_neg hq]
          exact AtomHom.zero_comp hD _)
      _ = Hom.id dD (S i) k l := by
        rw [Hom.id, dif_neg hkl, familyInclusion, dif_pos rfl,
          familyProjection, dif_neg hpack]
        exact AtomHom.comp_zero hD _

theorem familyInclusion_projection_ne {dD : DData} (hD : DLaws dD)
    {n : ℕ} (S : Fin n → Obj) (i j : Fin n) (hij : i ≠ j) :
    Hom.comp (familyInclusion (dD := dD) S i) (familyProjection S j) =
      Hom.zero dD (S i) (S j) := by
  classical
  letI : Fact (DLaws dD) := ⟨hD⟩
  funext k l
  rw [Hom.comp, AtomHom.finSum_eq_sum]
  have hpack : packIndex S i k ≠ packIndex S j l := by
    intro hp
    have hs := (pack S).injective hp
    exact hij (congrArg Sigma.fst hs)
  calc
    (∑ q, AtomHom.comp (familyInclusion S i k q)
        (familyProjection S j q l)) =
        AtomHom.comp
          (familyInclusion S i k (packIndex S i k))
          (familyProjection S j (packIndex S i k) l) :=
      Fintype.sum_eq_single _ (by
        intro q hq
        rw [familyInclusion, dif_neg hq]
        exact AtomHom.zero_comp hD _)
    _ = Hom.zero dD (S i) (S j) k l := by
      rw [familyInclusion, dif_pos rfl, familyProjection, dif_neg hpack]
      exact AtomHom.comp_zero hD _

theorem familyProjection_inclusion_total [Fact (DLaws x.D)]
    {n : ℕ} (S : Fin n → Obj) :
    (Candidate.data x rows).finSum n (fun i =>
        Hom.comp (familyProjection (dD := x.D) S i) (familyInclusion S i)) =
      Hom.id x.D (sumObj S) := by
  classical
  rw [candidateFinSum_eq_sum x rows]
  funext q r
  simp only [Finset.sum_apply]
  obtain ⟨⟨i, k⟩, rfl⟩ := (packObjEquiv S).surjective q
  obtain ⟨⟨j, l⟩, rfl⟩ := (packObjEquiv S).surjective r
  by_cases hp : (⟨i, k⟩ : (i : Fin n) × Fin (S i).size) = ⟨j, l⟩
  · cases hp
    rw [Fintype.sum_eq_single i]
    · rw [Hom.comp, AtomHom.finSum_eq_sum,
        Fintype.sum_eq_single k]
      · simp [familyInclusion, familyProjection, Hom.id,
          atomEqHom_comp_symm (Fact.out : DLaws x.D)]
      · intro t htk
        have hpack : packIndex S i k ≠ packIndex S i t := by
          intro h
          have hs : (⟨i, k⟩ : (i : Fin n) × Fin (S i).size) = ⟨i, t⟩ :=
            (pack S).injective h
          cases hs
          exact htk rfl
        simp [familyProjection, hpack, AtomHom.zero_comp (Fact.out : DLaws x.D)]
    · intro u hui
      rw [Hom.comp, AtomHom.finSum_eq_sum]
      apply Finset.sum_eq_zero
      intro t _
      have hpack : packIndex S i k ≠ packIndex S u t := by
        intro h
        have hs := (pack S).injective h
        exact hui (congrArg Sigma.fst hs).symm
      simp [familyProjection, hpack, AtomHom.zero_comp (Fact.out : DLaws x.D)]
  · have hqr : packIndex S i k ≠ packIndex S j l := by
      intro h
      exact hp ((pack S).injective h)
    rw [Fintype.sum_eq_single i]
    · rw [Hom.comp, AtomHom.finSum_eq_sum,
        Fintype.sum_eq_single k]
      · have hrq : packIndex S j l ≠ packIndex S i k := Ne.symm hqr
        simp [familyInclusion, familyProjection, Hom.id, hqr, hrq,
          AtomHom.comp_zero (Fact.out : DLaws x.D)]
      · intro t htk
        have hpack : packIndex S i k ≠ packIndex S i t := by
          intro h
          have hs : (⟨i, k⟩ : (i : Fin n) × Fin (S i).size) = ⟨i, t⟩ :=
            (pack S).injective h
          cases hs
          exact htk rfl
        simp [familyProjection, hpack, AtomHom.zero_comp (Fact.out : DLaws x.D)]
    · intro u hui
      rw [Hom.comp, AtomHom.finSum_eq_sum]
      apply Finset.sum_eq_zero
      intro t _
      have hpack : packIndex S i k ≠ packIndex S u t := by
        intro h
        have hs := (pack S).injective h
        exact hui (congrArg Sigma.fst hs).symm
      simp [familyProjection, hpack, AtomHom.zero_comp (Fact.out : DLaws x.D)]

/-- Canonical raw biproduct witness. -/
def biproductWitness (hD : DLaws x.D) {n : ℕ} (S : Fin n → Obj) :
    (Candidate.data x rows).BiproductWitness S := by
  letI : Fact (DLaws x.D) := ⟨hD⟩
  exact
    { object := sumObj S
      inclusion := familyInclusion S
      projection := familyProjection S
      inclusion_even := familyInclusion_even hD S
      projection_even := familyProjection_even hD S
      inclusion_projection_self := familyInclusion_projection_self hD S
      inclusion_projection_ne := familyInclusion_projection_ne hD S
      projection_inclusion_total := familyProjection_inclusion_total x rows S }

theorem has_finite_biproducts (hD : DLaws x.D) {n : ℕ}
    (S : Fin n → Obj) :
    Nonempty ((Candidate.data x rows).BiproductWitness S) :=
  ⟨biproductWitness x rows hD S⟩

/-! ## Decomposition into listed atoms -/

/-- The singleton objects listed by a coordinate object. -/
def atomSingletons (X : Obj) : Fin X.size → Obj :=
  fun i => Obj.singleton (X.atom i)

/-- The unique displayed coordinate of a singleton object. -/
def singletonIndex (A : Atom) : Fin (Obj.singleton A).size :=
  ⟨0, by simp⟩

theorem eq_singletonIndex (A : Atom) (i : Fin (Obj.singleton A).size) :
    i = singletonIndex A := by
  apply Fin.ext
  simp [singletonIndex]

/-- Inclusion of one listed atom into its tuple. -/
def atomInclusion {dD : DData} (X : Obj) (i : Fin X.size) :
    Hom dD (Obj.singleton (X.atom i)) X := fun _ j =>
  if h : j = i then by
    subst j
    exact atomEqHom (singleton_atom (X.atom i) _)
  else AtomHom.zero dD _ _

/-- Projection from a tuple onto one listed atom. -/
def atomProjection {dD : DData} (X : Obj) (i : Fin X.size) :
    Hom dD X (Obj.singleton (X.atom i)) := fun j _ =>
  if h : j = i then by
    subst j
    exact atomEqHom (singleton_atom (X.atom i) _).symm
  else AtomHom.zero dD _ _

theorem atomInclusion_even {dD : DData} (hD : DLaws dD)
    (X : Obj) (i : Fin X.size) :
    Hom.MemGrade 0 (atomInclusion (dD := dD) X i) := by
  intro k j
  by_cases h : j = i
  · subst j
    have hk : k = singletonIndex (X.atom i) := eq_singletonIndex _ _
    subst k
    rw [atomInclusion, dif_pos rfl]
    exact AtomHom.id_even hD (X.atom i)
  · simp [atomInclusion, h]
    exact AtomHom.zero_memGrade hD 0

theorem atomProjection_even {dD : DData} (hD : DLaws dD)
    (X : Obj) (i : Fin X.size) :
    Hom.MemGrade 0 (atomProjection (dD := dD) X i) := by
  intro j k
  by_cases h : j = i
  · subst j
    have hk : k = singletonIndex (X.atom i) := eq_singletonIndex _ _
    subst k
    rw [atomProjection, dif_pos rfl]
    exact AtomHom.id_even hD (X.atom i)
  · simp [atomProjection, h]
    exact AtomHom.zero_memGrade hD 0

theorem atomInclusion_projection_self {dD : DData} (hD : DLaws dD)
    (X : Obj) (i : Fin X.size) :
    Hom.comp (atomInclusion (dD := dD) X i) (atomProjection X i) =
      Hom.id dD (Obj.singleton (X.atom i)) := by
  classical
  letI : Fact (DLaws dD) := ⟨hD⟩
  funext k l
  have hk : k = singletonIndex (X.atom i) := eq_singletonIndex _ _
  have hl : l = singletonIndex (X.atom i) := eq_singletonIndex _ _
  subst k
  subst l
  rw [Hom.comp, AtomHom.finSum_eq_sum]
  calc
    (∑ q, AtomHom.comp
        (atomInclusion X i (singletonIndex (X.atom i)) q)
        (atomProjection X i q (singletonIndex (X.atom i)))) =
        AtomHom.comp
          (atomInclusion X i (singletonIndex (X.atom i)) i)
          (atomProjection X i i (singletonIndex (X.atom i))) :=
      Fintype.sum_eq_single i (by
        intro q hq
        rw [atomInclusion, dif_neg hq]
        exact AtomHom.zero_comp hD _)
    _ = Hom.id dD (Obj.singleton (X.atom i))
        (singletonIndex (X.atom i)) (singletonIndex (X.atom i)) := by
      rw [atomInclusion, dif_pos rfl, atomProjection, dif_pos rfl,
        Hom.id, dif_pos rfl]
      exact AtomHom.comp_id hD _

theorem atomInclusion_projection_ne {dD : DData} (hD : DLaws dD)
    (X : Obj) (i j : Fin X.size) (hij : i ≠ j) :
    Hom.comp (atomInclusion (dD := dD) X i) (atomProjection X j) =
      Hom.zero dD (Obj.singleton (X.atom i)) (Obj.singleton (X.atom j)) := by
  classical
  letI : Fact (DLaws dD) := ⟨hD⟩
  funext k l
  have hk : k = singletonIndex (X.atom i) := eq_singletonIndex _ _
  have hl : l = singletonIndex (X.atom j) := eq_singletonIndex _ _
  subst k
  subst l
  rw [Hom.comp, AtomHom.finSum_eq_sum]
  calc
    (∑ q, AtomHom.comp
        (atomInclusion X i (singletonIndex (X.atom i)) q)
        (atomProjection X j q (singletonIndex (X.atom j)))) =
        AtomHom.comp
          (atomInclusion X i (singletonIndex (X.atom i)) i)
          (atomProjection X j i (singletonIndex (X.atom j))) :=
      Fintype.sum_eq_single i (by
        intro q hq
        rw [atomInclusion, dif_neg hq]
        exact AtomHom.zero_comp hD _)
    _ = Hom.zero dD (Obj.singleton (X.atom i))
        (Obj.singleton (X.atom j))
          (singletonIndex (X.atom i)) (singletonIndex (X.atom j)) := by
      rw [atomInclusion, dif_pos rfl, atomProjection, dif_neg hij]
      exact AtomHom.comp_zero hD _

/-- The reverse composite contributes the identity at its selected diagonal
matrix entry. -/
theorem atomProjection_inclusion_self {dD : DData} (hD : DLaws dD)
    (X : Obj) (i : Fin X.size) :
    Hom.comp (atomProjection (dD := dD) X i) (atomInclusion X i) i i =
      AtomHom.id dD (X.atom i) := by
  rw [Hom.comp]
  calc
    AtomHom.finSum (Obj.singleton (X.atom i)).size (fun j =>
        AtomHom.comp (atomProjection X i i j) (atomInclusion X i j i)) =
        AtomHom.finSum (Obj.singleton (X.atom i)).size (fun j =>
          if j = singletonIndex (X.atom i) then
            AtomHom.comp
              (atomProjection X i i (singletonIndex (X.atom i)))
              (atomInclusion X i (singletonIndex (X.atom i)) i)
          else AtomHom.zero dD (X.atom i) (X.atom i)) := by
      apply AtomHom.finSum_congr
      intro j
      have hj : j = singletonIndex (X.atom i) := eq_singletonIndex _ _
      subst j
      rw [if_pos rfl, atomProjection, dif_pos rfl,
        atomInclusion, dif_pos rfl]
    _ = AtomHom.comp
        (atomProjection X i i (singletonIndex (X.atom i)))
        (atomInclusion X i (singletonIndex (X.atom i)) i) :=
      AtomHom.finSum_single hD (singletonIndex (X.atom i)) _
    _ = AtomHom.id dD (X.atom i) := by
      rw [atomProjection, dif_pos rfl, atomInclusion, dif_pos rfl]
      exact atomEqHom_comp_symm hD
        (singleton_atom (X.atom i) (singletonIndex (X.atom i))).symm

/-- Away from the selected source row, the reverse composite is zero. -/
theorem atomProjection_inclusion_source_ne {dD : DData} (hD : DLaws dD)
    (X : Obj) (i q r : Fin X.size) (hqi : q ≠ i) :
    Hom.comp (atomProjection (dD := dD) X i) (atomInclusion X i) q r =
      AtomHom.zero dD (X.atom q) (X.atom r) := by
  rw [Hom.comp]
  calc
    AtomHom.finSum (Obj.singleton (X.atom i)).size (fun j =>
        AtomHom.comp (atomProjection X i q j) (atomInclusion X i j r)) =
        AtomHom.finSum (Obj.singleton (X.atom i)).size (fun _ =>
          AtomHom.zero dD (X.atom q) (X.atom r)) := by
      apply AtomHom.finSum_congr
      intro j
      rw [atomProjection, dif_neg hqi]
      exact AtomHom.zero_comp hD _
    _ = AtomHom.zero dD (X.atom q) (X.atom r) :=
      AtomHom.finSum_zero hD _

/-- Away from the selected target column, the reverse composite is zero. -/
theorem atomProjection_inclusion_target_ne {dD : DData} (hD : DLaws dD)
    (X : Obj) (i q r : Fin X.size) (hri : r ≠ i) :
    Hom.comp (atomProjection (dD := dD) X i) (atomInclusion X i) q r =
      AtomHom.zero dD (X.atom q) (X.atom r) := by
  rw [Hom.comp]
  calc
    AtomHom.finSum (Obj.singleton (X.atom i)).size (fun j =>
        AtomHom.comp (atomProjection X i q j) (atomInclusion X i j r)) =
        AtomHom.finSum (Obj.singleton (X.atom i)).size (fun _ =>
          AtomHom.zero dD (X.atom q) (X.atom r)) := by
      apply AtomHom.finSum_congr
      intro j
      rw [atomInclusion, dif_neg hri]
      exact AtomHom.comp_zero hD _
    _ = AtomHom.zero dD (X.atom q) (X.atom r) :=
      AtomHom.finSum_zero hD _

theorem atomProjection_inclusion_total [Fact (DLaws x.D)] (X : Obj) :
    (Candidate.data x rows).finSum X.size (fun i =>
        Hom.comp (atomProjection (dD := x.D) X i) (atomInclusion X i)) =
      Hom.id x.D X := by
  classical
  rw [candidateFinSum_eq_sum x rows]
  funext q r
  simp only [Finset.sum_apply]
  by_cases hqr : q = r
  · subst r
    rw [Fintype.sum_eq_single q (by
      intro i hi
      exact atomProjection_inclusion_source_ne (Fact.out : DLaws x.D)
        X i q q (Ne.symm hi))]
    rw [atomProjection_inclusion_self (Fact.out : DLaws x.D), Hom.id,
      dif_pos rfl]
  · calc
      (∑ i, Hom.comp (atomProjection X i) (atomInclusion X i) q r) =
          Hom.comp (atomProjection X q) (atomInclusion X q) q r :=
        Fintype.sum_eq_single q (by
          intro i hi
          exact atomProjection_inclusion_source_ne (Fact.out : DLaws x.D)
            X i q r (Ne.symm hi))
      _ = Hom.id x.D X q r := by
        rw [atomProjection_inclusion_target_ne (Fact.out : DLaws x.D)
          X q q r (Ne.symm hqr), Hom.id, dif_neg hqr]

/-- The canonical decomposition witness for a coordinate tuple. -/
def atomDecompositionWitness (hD : DLaws x.D) (X : Obj) :
    (Candidate.data x rows).DecompositionWitness X (atomSingletons X) := by
  letI : Fact (DLaws x.D) := ⟨hD⟩
  exact
    { inclusion := atomInclusion X
      projection := atomProjection X
      inclusion_even := atomInclusion_even hD X
      projection_even := atomProjection_even hD X
      inclusion_projection_self := atomInclusion_projection_self hD X
      inclusion_projection_ne := atomInclusion_projection_ne hD X
      projection_inclusion_total := atomProjection_inclusion_total x rows X }

/-- Semisimplicity reduces to simplicity of singleton atoms. -/
theorem semisimple_of_singletons_simple (hD : DLaws x.D)
    (hsimple : ∀ A : Atom,
      (Candidate.data x rows).IsSimple (Obj.singleton A))
    (X : Obj) :
    ∃ (n : ℕ) (S : Fin n → Obj),
      (∀ i, (Candidate.data x rows).IsSimple (S i)) ∧
        Nonempty ((Candidate.data x rows).DecompositionWitness X S) :=
  ⟨X.size, atomSingletons X, fun i => hsimple (X.atom i),
    ⟨atomDecompositionWitness x rows hD X⟩⟩

end Finite

end Superfusion.RMod.FromRawDCT
