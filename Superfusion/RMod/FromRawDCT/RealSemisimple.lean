import Superfusion.RMod.FromRawDCT.RealDivision

/-!
# Simplicity and semisimplicity of the shifted real candidate

A nonzero homogeneous map to one coordinate atom contains a nonzero
homogeneous coefficient.  Super-division supplies an inverse coefficient,
hence a homogeneous section.  The canonical finite tuple decomposition then
makes every object a finite direct sum of simple singleton atoms.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT
open RModCoordinate
open CandidateData

namespace RealSemisimple

private abbrev realShiftedD : DData :=
  realDData

/-! ## Nonzero atomic coefficients -/

namespace AtomHom

/-- A nonzero atomic quotient forces equality of its endpoint labels. -/
theorem label_eq_of_ne_zero {X Y : Atom} {f : AtomHom realShiftedD X Y}
    (hf : f ≠ AtomHom.zero realShiftedD X Y) :
    Atom.label X = Atom.label Y := by
  by_contra hXY
  exact hf (AtomHom.eq_of_label_ne hXY f
    (AtomHom.zero realShiftedD X Y))

/-- At equal labels, the unique stored coefficient of a nonzero atomic map is
nonzero. -/
theorem coeff_ne_zero {X Y : Atom} {f : AtomHom realShiftedD X Y}
    (hf : f ≠ AtomHom.zero realShiftedD X Y) :
    f.coeff (label_eq_of_ne_zero hf) ≠
      (realShiftedD.algebra (Atom.label X)).zero := by
  intro hcoeff
  apply hf
  apply AtomHom.ext
  intro hXY
  rw [AtomHom.coeff_zero]
  simpa only [Subsingleton.elim hXY (label_eq_of_ne_zero hf)] using hcoeff

/-- Inserting a homogeneous coefficient at a common endpoint gives a
homogeneous atomic quotient. -/
theorem ofLabelEq_memGrade {X Y : Atom}
    (hXY : Atom.label X = Atom.label Y) (d : ZMod 2)
    (x : (realShiftedD.algebra (Atom.label X)).carrier)
    (hx : (realShiftedD.algebra (Atom.label X)).MemGrade
      (d + Atom.shift X + Atom.shift Y) x) :
    AtomHom.MemGrade (dD := realShiftedD) d
      (AtomHom.ofLabelEq (dD := realShiftedD) hXY x) := by
  intro h
  simpa only [Subsingleton.elim h hXY, AtomHom.coeff_ofLabelEq] using hx

end AtomHom

/-! ## Elementary even maps -/

/-- The identity of a singleton coordinate atom is nonzero. -/
theorem singleton_id_ne_zero (A : Atom) :
    realCandidateData.id (Obj.singleton A) ≠
      realCandidateData.zero := by
  intro h
  change Hom.id realShiftedD (Obj.singleton A) =
    Hom.zero realShiftedD (Obj.singleton A) (Obj.singleton A) at h
  have hentry := congrFun
    (congrFun h (Finite.singletonIndex A)) (Finite.singletonIndex A)
  have hentry' : AtomHom.id realShiftedD A =
      AtomHom.zero realShiftedD A A := by
    simpa [Hom.id, Hom.zero, Finite.singletonIndex, Obj.singleton,
      Obj.atom] using hentry
  have hcoeff := congrArg (fun q => q.coeff rfl) hentry'
  rw [AtomHom.coeff_id, AtomHom.coeff_zero] at hcoeff
  have hzero := congrFun hcoeff
    (⟨0, realRepDim_pos A.1.val⟩ : Fin (realRepDim A.1.val))
  simpa [realShiftedD, realDData, coordinateSuperAlgebraData,
    Coeff.one, Coeff.zero, Atom.label] using hzero

/-- The identity is an even monomorphism in the raw even subcategory. -/
theorem id_evenMono (X : Obj) :
    realCandidateData.IsEvenMono (realCandidateData.id X) := by
  refine ⟨?_, ?_⟩
  · change Hom.MemGrade 0 (Hom.id realShiftedD X)
    exact Hom.id_even realComputableShiftedRawDCT.laws.D X
  · change ∀ (Z : Obj) (f g : Hom realShiftedD Z X),
      Hom.MemGrade 0 f → Hom.MemGrade 0 g →
        Hom.comp f (Hom.id realShiftedD X) =
          Hom.comp g (Hom.id realShiftedD X) → f = g
    intro Z f g _ _ h
    change Hom.comp f (Hom.id realShiftedD X) =
      Hom.comp g (Hom.id realShiftedD X) at h
    calc
      f = Hom.comp f (Hom.id realShiftedD X) :=
        (Hom.comp_id realDLaws f).symm
      _ = Hom.comp g (Hom.id realShiftedD X) := h
      _ = g := Hom.comp_id realDLaws g

/-- The identity is an even isomorphism. -/
theorem id_evenIso (X : Obj) :
    realCandidateData.IsEvenIso (realCandidateData.id X) := by
  refine ⟨?_, realCandidateData.id X, ?_, ?_, ?_⟩
  · change Hom.MemGrade 0 (Hom.id realShiftedD X)
    exact Hom.id_even realComputableShiftedRawDCT.laws.D X
  · change Hom.MemGrade 0 (Hom.id realShiftedD X)
    exact Hom.id_even realComputableShiftedRawDCT.laws.D X
  · change Hom.comp (Hom.id realShiftedD X) (Hom.id realShiftedD X) = _
    exact Hom.comp_id realComputableShiftedRawDCT.laws.D _
  · change Hom.comp (Hom.id realShiftedD X) (Hom.id realShiftedD X) = _
    exact Hom.comp_id realComputableShiftedRawDCT.laws.D _

/-- A simple object has nonzero identity. -/
theorem simple_id_ne_zero {X : Obj}
    (hX : realCandidateData.IsSimple X) :
    realCandidateData.id X ≠ realCandidateData.zero :=
  (hX X (realCandidateData.id X) (id_evenMono X)).mp (id_evenIso X)

/-! ## Canonical atomic inclusions -/

/-- Inclusion of one listed atom is an even monomorphism. -/
theorem atomInclusion_evenMono (X : Obj) (i : Fin X.size) :
    realCandidateData.IsEvenMono
      (Finite.atomInclusion (dD := realShiftedD) X i) := by
  refine ⟨Finite.atomInclusion_even realDLaws X i, ?_⟩
  change ∀ (Z : Obj)
      (f g : Hom realShiftedD Z (Obj.singleton (X.atom i))),
    Hom.MemGrade 0 f → Hom.MemGrade 0 g →
      Hom.comp f (Finite.atomInclusion X i) =
        Hom.comp g (Finite.atomInclusion X i) → f = g
  intro Z f g _ _ h
  have h' := congrArg
    (fun k => Hom.comp k (Finite.atomProjection (dD := realShiftedD) X i)) h
  calc
    f = Hom.comp f (Hom.id realShiftedD (Obj.singleton (X.atom i))) :=
      (Hom.comp_id realDLaws f).symm
    _ = Hom.comp f
        (Hom.comp (Finite.atomInclusion X i) (Finite.atomProjection X i)) := by
      rw [Finite.atomInclusion_projection_self realDLaws]
    _ = Hom.comp (Hom.comp f (Finite.atomInclusion X i))
        (Finite.atomProjection X i) :=
      (Hom.comp_assoc realDLaws _ _ _).symm
    _ = Hom.comp (Hom.comp g (Finite.atomInclusion X i))
        (Finite.atomProjection X i) := h'
    _ = Hom.comp g
        (Hom.comp (Finite.atomInclusion X i) (Finite.atomProjection X i)) :=
      Hom.comp_assoc realDLaws _ _ _
    _ = Hom.comp g (Hom.id realShiftedD (Obj.singleton (X.atom i))) := by
      rw [Finite.atomInclusion_projection_self realDLaws]
    _ = g := Hom.comp_id realDLaws g

/-- A canonical inclusion cannot vanish. -/
theorem atomInclusion_ne_zero (X : Obj) (i : Fin X.size) :
    Finite.atomInclusion (dD := realShiftedD) X i ≠
      Hom.zero realShiftedD (Obj.singleton (X.atom i)) X := by
  intro h
  apply singleton_id_ne_zero (X.atom i)
  change Hom.id realShiftedD (Obj.singleton (X.atom i)) =
    Hom.zero realShiftedD (Obj.singleton (X.atom i))
      (Obj.singleton (X.atom i))
  calc
    Hom.id realShiftedD (Obj.singleton (X.atom i)) =
        Hom.comp (Finite.atomInclusion X i) (Finite.atomProjection X i) :=
      (Finite.atomInclusion_projection_self realDLaws X i).symm
    _ = Hom.comp (Hom.zero realShiftedD (Obj.singleton (X.atom i)) X)
        (Finite.atomProjection X i) := by rw [h]
    _ = Hom.zero realShiftedD (Obj.singleton (X.atom i))
        (Obj.singleton (X.atom i)) :=
      Hom.zero_comp realDLaws _

/-- A simple coordinate tuple has exactly one listed atomic summand. -/
theorem simple_card_eq_one {X : Obj}
    (hX : realCandidateData.IsSimple X) : X.size = 1 := by
  have hn0 : X.size ≠ 0 := by
    intro hn
    apply simple_id_ne_zero hX
    change Hom.id realShiftedD X = Hom.zero realShiftedD X X
    funext i
    exact Fin.elim0 (hn ▸ i)
  let i : Fin X.size := ⟨0, Nat.pos_of_ne_zero hn0⟩
  have hiIso : realCandidateData.IsEvenIso
      (Finite.atomInclusion (dD := realShiftedD) X i) :=
    (hX _ _ (atomInclusion_evenMono X i)).mpr
      (atomInclusion_ne_zero X i)
  rcases hiIso with ⟨_, g, _, _, hgi⟩
  change Hom realShiftedD X (Obj.singleton (X.atom i)) at g
  change Hom.comp g (Finite.atomInclusion X i) =
    Hom.id realShiftedD X at hgi
  have hall : ∀ j : Fin X.size, j = i := by
    intro j
    by_contra hji
    have hij : i ≠ j := fun hij => hji hij.symm
    apply singleton_id_ne_zero (X.atom j)
    change Hom.id realShiftedD (Obj.singleton (X.atom j)) =
      Hom.zero realShiftedD (Obj.singleton (X.atom j))
        (Obj.singleton (X.atom j))
    calc
      Hom.id realShiftedD (Obj.singleton (X.atom j)) =
          Hom.comp (Finite.atomInclusion X j) (Finite.atomProjection X j) :=
        (Finite.atomInclusion_projection_self realDLaws X j).symm
      _ = Hom.comp
            (Hom.comp (Finite.atomInclusion X j)
              (Hom.comp g (Finite.atomInclusion X i)))
            (Finite.atomProjection X j) := by
          rw [hgi, Hom.comp_id realDLaws]
      _ = Hom.comp
            (Hom.comp
              (Hom.comp (Finite.atomInclusion X j) g)
              (Finite.atomInclusion X i))
            (Finite.atomProjection X j) := by
          rw [← Hom.comp_assoc realDLaws]
      _ = Hom.comp
            (Hom.comp (Finite.atomInclusion X j) g)
            (Hom.comp (Finite.atomInclusion X i)
              (Finite.atomProjection X j)) := by
          rw [Hom.comp_assoc realDLaws]
      _ = Hom.comp
            (Hom.comp (Finite.atomInclusion X j) g)
            (Hom.zero realShiftedD (Obj.singleton (X.atom i))
              (Obj.singleton (X.atom j))) := by
          rw [Finite.atomInclusion_projection_ne realDLaws X i j hij]
      _ = Hom.zero realShiftedD (Obj.singleton (X.atom j))
            (Obj.singleton (X.atom j)) := Hom.comp_zero realDLaws _
  letI : Subsingleton (Fin X.size) :=
    ⟨fun j k => (hall j).trans (hall k).symm⟩
  have hle : X.size ≤ 1 := by
    simpa using
      (Fintype.card_le_one_iff_subsingleton.mpr
        (inferInstance : Subsingleton (Fin X.size)))
  omega

/-! ## Homogeneous sections from super-division -/

/-- A nonzero homogeneous atomic map has a homogeneous two-sided inverse. -/
theorem exists_homogeneous_atomic_inverse
    {X Y : Atom} {d : ZMod 2}
    (f : AtomHom realShiftedD X Y)
    (hfgrade : AtomHom.MemGrade d f)
    (hf0 : f ≠ AtomHom.zero realShiftedD X Y) :
    ∃ g : AtomHom realShiftedD Y X,
      AtomHom.MemGrade d g ∧
        AtomHom.comp f g = AtomHom.id realShiftedD X ∧
        AtomHom.comp g f = AtomHom.id realShiftedD Y := by
  rcases X with ⟨a, s⟩
  rcases Y with ⟨b, t⟩
  have hab := AtomHom.label_eq_of_ne_zero hf0
  change a = b at hab
  subst b
  let x : Coeff a := f.coeff rfl
  have hx0 : x ≠ Coeff.zero a := by
    have h := AtomHom.coeff_ne_zero hf0
    simpa [x, realShiftedD, realDData, coordinateSuperAlgebraData,
      Atom.label] using h
  have hxgrade : Coeff.MemGrade a (d + s + t) x := by
    apply (Coeff.component_eq_self_iff a (d + s + t) x).mp
    have h := hfgrade rfl
    simpa [x, realShiftedD, realDData, coordinateSuperAlgebraData,
      SuperAlgebraData.MemGrade, Atom.label, Atom.shift] using h
  obtain ⟨y, hygrade, hyx, hxy⟩ :=
    RealDivision.exists_homogeneous_inverse a (d + s + t) x hxgrade hx0
  let g : AtomHom realShiftedD (a, t) (a, s) :=
    AtomHom.ofLabelEq rfl y
  refine ⟨g, ?_, ?_, ?_⟩
  · apply AtomHom.ofLabelEq_memGrade
      (X := (a, t)) (Y := (a, s)) rfl d y
    apply (Coeff.component_eq_self_iff a (d + t + s) y).mpr
    simpa only [add_assoc, add_left_comm, add_comm] using hygrade
  · apply AtomHom.ext_same_label
    simpa [g, x, realShiftedD, realDData, coordinateSuperAlgebraData,
      Atom.label] using hyx
  · apply AtomHom.ext_same_label
    simpa [g, x, realShiftedD, realDData, coordinateSuperAlgebraData,
      Atom.label] using hxy

/-- A nonzero homogeneous matrix map to a singleton atom admits a
homogeneous section of the same categorical degree. -/
theorem exists_homogeneous_section_to_singleton
    {Y : Obj} {A : Atom} {d : ZMod 2}
    (f : Hom realShiftedD Y (Obj.singleton A))
    (hfgrade : Hom.MemGrade d f)
    (hf0 : f ≠ Hom.zero realShiftedD Y (Obj.singleton A)) :
    ∃ g : Hom realShiftedD (Obj.singleton A) Y,
      Hom.MemGrade d g ∧
        Hom.comp g f = Hom.id realShiftedD (Obj.singleton A) := by
  classical
  have hex : ∃ i : Fin Y.size,
      f i (Finite.singletonIndex A) ≠
        AtomHom.zero realShiftedD (Y.atom i) A := by
    by_contra h
    push Not at h
    apply hf0
    funext i j
    have hj : j = Finite.singletonIndex A := Finite.eq_singletonIndex A j
    subst j
    simpa [Hom.zero, Obj.singleton, Obj.atom, Finite.singletonIndex] using h i
  obtain ⟨i, hfi0⟩ := hex
  obtain ⟨gi, hgigrade, _, hgif⟩ :=
    exists_homogeneous_atomic_inverse
      (f i (Finite.singletonIndex A))
      (hfgrade i (Finite.singletonIndex A)) hfi0
  let g : Hom realShiftedD (Obj.singleton A) Y := fun q j =>
    if hji : j = i then by
      subst j
      have hq : q = Finite.singletonIndex A :=
        Finite.eq_singletonIndex A q
      subst q
      exact gi
    else AtomHom.zero realShiftedD _ _
  refine ⟨g, ?_, ?_⟩
  · intro q j
    have hq : q = Finite.singletonIndex A := Finite.eq_singletonIndex A q
    subst q
    by_cases hji : j = i
    · subst j
      simpa [g] using hgigrade
    · simp [g, hji]
      exact AtomHom.zero_memGrade realDLaws d
  · apply Hom.ext
    intro q r
    have hq : q = Finite.singletonIndex A := Finite.eq_singletonIndex A q
    have hr : r = Finite.singletonIndex A := Finite.eq_singletonIndex A r
    subst q
    subst r
    rw [Hom.comp, AtomHom.finSum_eq_sum, Fintype.sum_eq_single i]
    · simpa [g, Hom.id, Finite.singletonIndex, Obj.singleton, Obj.atom]
        using hgif
    · intro j hji
      have hg : g (Finite.singletonIndex A) j =
          AtomHom.zero realShiftedD A (Y.atom j) := by
        simp [g, hji, Finite.singletonIndex, Obj.singleton, Obj.atom]
      rw [hg]
      exact AtomHom.zero_comp realDLaws _

/-! ## Simplicity and semisimplicity -/

/-- Every singleton coordinate atom is simple in the even subcategory. -/
theorem singleton_simple (A : Atom) :
    realCandidateData.IsSimple (Obj.singleton A) := by
  intro Y f hfmono
  change Hom realShiftedD Y (Obj.singleton A) at f
  change Hom.MemGrade 0 f ∧
    ∀ (Z : Obj) (g h : Hom realShiftedD Z Y),
      Hom.MemGrade 0 g → Hom.MemGrade 0 h →
        Hom.comp g f = Hom.comp h f → g = h at hfmono
  change
    (Hom.MemGrade 0 f ∧
      ∃ g : Hom realShiftedD (Obj.singleton A) Y,
        Hom.MemGrade 0 g ∧
          Hom.comp f g = Hom.id realShiftedD Y ∧
          Hom.comp g f = Hom.id realShiftedD (Obj.singleton A)) ↔
      f ≠ Hom.zero realShiftedD Y (Obj.singleton A)
  constructor
  · rintro ⟨_, g, _, _, hgf⟩ hfzero
    apply singleton_id_ne_zero A
    change Hom.id realShiftedD (Obj.singleton A) =
      Hom.zero realShiftedD (Obj.singleton A) (Obj.singleton A)
    calc
      Hom.id realShiftedD (Obj.singleton A) = Hom.comp g f := hgf.symm
      _ = Hom.comp g (Hom.zero realShiftedD Y (Obj.singleton A)) := by
        rw [hfzero]
      _ = Hom.zero realShiftedD (Obj.singleton A) (Obj.singleton A) :=
        Hom.comp_zero realDLaws g
  · intro hf0
    obtain ⟨g, hggrade, hgf⟩ :=
      exists_homogeneous_section_to_singleton f hfmono.1 hf0
    have hfggrade : Hom.MemGrade 0 (Hom.comp f g) := by
      simpa using Hom.comp_memGrade realDLaws f g hfmono.1 hggrade
    have hfg : Hom.comp f g = Hom.id realShiftedD Y := by
      apply hfmono.2 Y (Hom.comp f g) (Hom.id realShiftedD Y)
      · exact hfggrade
      · exact Hom.id_even realDLaws Y
      · calc
          Hom.comp (Hom.comp f g) f = Hom.comp f (Hom.comp g f) :=
            Hom.comp_assoc realDLaws f g f
          _ = Hom.comp f (Hom.id realShiftedD (Obj.singleton A)) := by
            rw [hgf]
          _ = f := Hom.comp_id realDLaws f
          _ = Hom.comp (Hom.id realShiftedD Y) f :=
            (Hom.id_comp realDLaws f).symm
    exact ⟨hfmono.1, g, hggrade, hfg, hgf⟩

/-- Every finite coordinate object is a finite direct sum of simple
singletons. -/
theorem real_semisimple (X : Obj) :
    ∃ (n : ℕ) (S : Fin n → Obj),
      (∀ i, realCandidateData.IsSimple (S i)) ∧
        Nonempty (realCandidateData.DecompositionWitness X S) := by
  exact Finite.semisimple_of_singletons_simple
    realComputableShiftedRawDCT.data realUnitRowsData
    realComputableShiftedRawDCT.laws.D singleton_simple X

/-! ## Classification of simple coordinate objects -/

/-- A simple tuple is evenly isomorphic to its unique singleton summand. -/
theorem simple_iso_atom {X : Obj}
    (hX : realCandidateData.IsSimple X) :
    ∃ i : Fin X.size,
      Nonempty (realCandidateData.HomogeneousIso 0 X
        (Obj.singleton (X.atom i))) := by
  have hn : X.size = 1 := simple_card_eq_one hX
  let i : Fin X.size := ⟨0, by omega⟩
  have hiIso : realCandidateData.IsEvenIso
      (Finite.atomInclusion (dD := realShiftedD) X i) :=
    (hX _ _ (atomInclusion_evenMono X i)).mpr
      (atomInclusion_ne_zero X i)
  rcases hiIso with ⟨hi, g, hg, hig, hgi⟩
  exact ⟨i, ⟨
    { hom := g
      inv := Finite.atomInclusion X i
      hom_inv := hgi
      inv_hom := hig
      hom_mem := hg
      inv_mem := hi }⟩⟩

/-- The sixteen label-and-shift atoms in a fixed computable order. -/
def atomFinEquiv : Atom ≃ Fin (8 * 2) :=
  (Equiv.prodCongr (ZMod.finEquiv 8).symm.toEquiv
      (ZMod.finEquiv 2).symm.toEquiv).trans finProdFinEquiv

/-- The singleton representative at one finite atom index. -/
def representative (i : Fin (8 * 2)) : Obj :=
  Obj.singleton (atomFinEquiv.symm i)

@[simp] theorem representative_atom (A : Atom) :
    representative (atomFinEquiv A) = Obj.singleton A := by
  simp [representative]

/-- Sixteen singleton atoms represent all simple coordinate objects, up to a
homogeneous (in fact even) isomorphism. -/
theorem finite_simple_representatives :
    ∃ (n : ℕ) (S : Fin n → Obj),
      (∀ i, realCandidateData.IsSimple (S i)) ∧
        ∀ X : Obj, realCandidateData.IsSimple X →
          ∃ (i : Fin n) (d : ZMod 2),
            Nonempty (realCandidateData.HomogeneousIso d X (S i)) := by
  refine ⟨8 * 2, representative, ?_, ?_⟩
  · intro i
    exact singleton_simple _
  · intro X hX
    obtain ⟨i, ⟨e⟩⟩ := simple_iso_atom hX
    refine ⟨atomFinEquiv (X.atom i), 0, ?_⟩
    simpa [representative] using (show
      Nonempty (realCandidateData.HomogeneousIso 0 X
        (Obj.singleton (X.atom i))) from ⟨e⟩)

/-! ## Graded Schur law -/

/-- Between simple coordinate tuples, a nonzero homogeneous matrix is
invertible.  Since both tuples have one entry, this is exactly the atomic
super-division inverse above. -/
theorem graded_schur_raw {X Y : Obj}
    (hX : realCandidateData.IsSimple X)
    (hY : realCandidateData.IsSimple Y)
    {d : ZMod 2} (f : Hom realShiftedD X Y)
    (hfgrade : Hom.MemGrade d f)
    (hf0 : f ≠ Hom.zero realShiftedD X Y) :
    ∃ g : Hom realShiftedD Y X,
      Hom.comp f g = Hom.id realShiftedD X ∧
        Hom.comp g f = Hom.id realShiftedD Y := by
  classical
  have hXsize : X.size = 1 := simple_card_eq_one hX
  have hYsize : Y.size = 1 := simple_card_eq_one hY
  let iX : Fin X.size := ⟨0, by omega⟩
  let iY : Fin Y.size := ⟨0, by omega⟩
  have hXindex : ∀ i : Fin X.size, i = iX := by
    intro i
    apply Fin.ext
    omega
  have hYindex : ∀ i : Fin Y.size, i = iY := by
    intro i
    apply Fin.ext
    omega
  have hfentry0 : f iX iY ≠
      AtomHom.zero realShiftedD (X.atom iX) (Y.atom iY) := by
    intro hentry
    apply hf0
    apply Hom.ext
    intro i j
    rw [hXindex i, hYindex j]
    exact hentry
  obtain ⟨gentry, hgentryGrade, hfgentry, hgfentry⟩ :=
    exists_homogeneous_atomic_inverse (f iX iY)
      (hfgrade iX iY) hfentry0
  let g : Hom realShiftedD Y X := fun i j => by
    rw [hYindex i, hXindex j]
    exact gentry
  refine ⟨g, ?_, ?_⟩
  · apply Hom.ext
    intro i j
    rw [hXindex i, hXindex j, Hom.comp, AtomHom.finSum_eq_sum,
      Fintype.sum_eq_single iY]
    · simpa [g, Hom.id] using hfgentry
    · intro k hk
      exact (hk (hYindex k)).elim
  · apply Hom.ext
    intro i j
    rw [hYindex i, hYindex j, Hom.comp, AtomHom.finSum_eq_sum,
      Fintype.sum_eq_single iX]
    · simpa [g, Hom.id] using hgfentry
    · intro k hk
      exact (hk (hXindex k)).elim

/-- The graded Schur field in the exact `CandidateLaws` form. -/
theorem graded_schur :
    ∀ {X Y : Obj}, realCandidateData.IsSimple X →
      realCandidateData.IsSimple Y →
      ∀ {d : ZMod 2} (f : realCandidateData.Hom X Y),
        realCandidateData.IsHomogeneous d f →
          f ≠ realCandidateData.zero → realCandidateData.IsIso f := by
  intro X Y hX hY d f hfgrade hf0
  change Hom realShiftedD X Y at f
  change Hom.MemGrade d f at hfgrade
  change f ≠ Hom.zero realShiftedD X Y at hf0
  obtain ⟨g, hfg, hgf⟩ := graded_schur_raw hX hY f hfgrade hf0
  exact ⟨g, hfg, hgf⟩

end RealSemisimple

end Superfusion.RMod.FromRawDCT
