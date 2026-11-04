import Superfusion.RMod.RawDCT.RawDCT

/-!
# Finite coordinate envelopes of raw coefficient families

This file contains only the abstract construction from a raw coefficient
family.  A simple atom is a label together with a parity shift, and an object
is a canonically indexed finite tuple of atoms.

The atomic Hom carrier deliberately contains no support proof.  It is the
quotient of all label-indexed coefficient families by equality at the common
endpoint label.  When the endpoint labels differ, the quotient is therefore
a singleton.  This is the proof-free replacement for the former mixed record
whose fields were a coefficient family and a `Prop`-valued support witness.
-/

set_option autoImplicit false

namespace Superfusion.RMod.FromRawDCT

open RawDCT

/-! ## Atoms and finite objects -/

/-- A skeletal label and a categorical parity shift. -/
abbrev Atom := ZMod 8 × ZMod 2

namespace Atom

def label (X : Atom) : ZMod 8 := X.1

def shift (X : Atom) : ZMod 2 := X.2

end Atom

/-- A canonically indexed finite tuple of atoms. -/
abbrev Obj := Σ n : ℕ, Fin n → Atom

namespace Obj

def size (X : Obj) : ℕ := X.1

def atom (X : Obj) : Fin X.size → Atom := X.2

/-- The empty additive object. -/
def zero : Obj := ⟨0, Fin.elim0⟩

/-- A one-summand additive object. -/
def singleton (X : Atom) : Obj := ⟨1, fun _ => X⟩

end Obj

/-! ## Proof-free atomic morphisms -/

/-- An unrestricted family of raw coefficients, used only before quotienting
away all components except a common endpoint label. -/
abbrev RawAtomHom (dD : DData) :=
  (a : ZMod 8) → (dD.algebra a).carrier

/-- Two unrestricted families represent the same atomic morphism when their
coefficients agree at the common endpoint.  If the endpoint labels differ,
the implication is vacuous and the quotient has exactly one element. -/
def atomHomSetoid (dD : DData) (X Y : Atom) : Setoid (RawAtomHom dD) where
  r f g := Atom.label X = Atom.label Y →
    f (Atom.label X) = g (Atom.label X)
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h hXY => (h hXY).symm
    trans := fun hfg hgh hXY => (hfg hXY).trans (hgh hXY) }

/-- Atomic morphisms with no `Prop` field in their executable carrier. -/
abbrev AtomHom (dD : DData) (X Y : Atom) :=
  @Quotient (RawAtomHom dD) (atomHomSetoid dD X Y)

namespace AtomHom

/-- Insert an unrestricted coefficient family into the atomic quotient. -/
def mk (dD : DData) (X Y : Atom) (f : RawAtomHom dD) : AtomHom dD X Y :=
  @Quotient.mk' (RawAtomHom dD) (atomHomSetoid dD X Y) f

/-- The defining quotient relation gives equality of atomic morphisms. -/
theorem sound {dD : DData} {X Y : Atom} {f g : RawAtomHom dD}
    (h : (atomHomSetoid dD X Y).r f g) :
    mk dD X Y f = mk dD X Y g :=
  @Quotient.sound (RawAtomHom dD) (atomHomSetoid dD X Y) f g h

/-- Read the coefficient at the common label. -/
def coeff {dD : DData} {X Y : Atom} (f : AtomHom dD X Y)
    (hXY : Atom.label X = Atom.label Y) :
    (dD.algebra (Atom.label X)).carrier :=
  Quotient.liftOn f (fun g => g (Atom.label X)) (by
    intro g g' hgg'
    exact hgg' hXY)

@[simp] theorem coeff_mk {dD : DData} {X Y : Atom}
    (f : RawAtomHom dD) (hXY : Atom.label X = Atom.label Y) :
    (mk dD X Y f).coeff hXY = f (Atom.label X) :=
  rfl

/-- Atomic morphisms are determined by their common-label coefficient. -/
@[ext] theorem ext {dD : DData} {X Y : Atom}
    {f g : AtomHom dD X Y}
    (h : ∀ hXY : Atom.label X = Atom.label Y,
      f.coeff hXY = g.coeff hXY) : f = g := by
  induction f using Quotient.inductionOn with
  | _ f =>
      induction g using Quotient.inductionOn with
      | _ g =>
          apply sound
          intro hXY
          exact h hXY

/-- If the endpoint labels differ, the atomic Hom quotient is a singleton. -/
theorem eq_of_label_ne {dD : DData} {X Y : Atom}
    (hXY : Atom.label X ≠ Atom.label Y) (f g : AtomHom dD X Y) : f = g := by
  apply ext
  intro h
  exact (hXY h).elim

/-- The zero atomic morphism. -/
def zero (dD : DData) (X Y : Atom) : AtomHom dD X Y :=
  mk dD X Y (fun a => (dD.algebra a).zero)

@[simp] theorem coeff_zero {dD : DData} {X Y : Atom}
    (hXY : Atom.label X = Atom.label Y) :
    (zero dD X Y).coeff hXY = (dD.algebra (Atom.label X)).zero :=
  rfl

/-- Pointwise addition before passing to the support quotient. -/
def add {dD : DData} {X Y : Atom}
    (f g : AtomHom dD X Y) : AtomHom dD X Y :=
  Quotient.liftOn₂ f g
    (fun f g => mk dD X Y (fun a => (dD.algebra a).add (f a) (g a))) (by
      intro f g f' g' hff' hgg'
      apply sound
      intro hXY
      change (dD.algebra (Atom.label X)).add
          (f (Atom.label X)) (g (Atom.label X)) =
        (dD.algebra (Atom.label X)).add
          (f' (Atom.label X)) (g' (Atom.label X))
      rw [hff' hXY, hgg' hXY])

@[simp] theorem coeff_add {dD : DData} {X Y : Atom}
    (f g : AtomHom dD X Y) (hXY : Atom.label X = Atom.label Y) :
    (add f g).coeff hXY =
      (dD.algebra (Atom.label X)).add (f.coeff hXY) (g.coeff hXY) := by
  induction f using Quotient.inductionOn with
  | _ f =>
      induction g using Quotient.inductionOn with
      | _ g => rfl

/-- Pointwise additive inverse before passing to the support quotient. -/
def neg {dD : DData} {X Y : Atom}
    (f : AtomHom dD X Y) : AtomHom dD X Y :=
  Quotient.liftOn f
    (fun f => mk dD X Y (fun a => (dD.algebra a).neg (f a))) (by
      intro f g hfg
      apply sound
      intro hXY
      change (dD.algebra (Atom.label X)).neg (f (Atom.label X)) =
        (dD.algebra (Atom.label X)).neg (g (Atom.label X))
      rw [hfg hXY])

@[simp] theorem coeff_neg {dD : DData} {X Y : Atom}
    (f : AtomHom dD X Y) (hXY : Atom.label X = Atom.label Y) :
    (neg f).coeff hXY = (dD.algebra (Atom.label X)).neg (f.coeff hXY) := by
  induction f using Quotient.inductionOn with
  | _ f => rfl

/-- Pointwise real scalar multiplication. -/
def smul {dD : DData} {X Y : Atom} (r : ℝ)
    (f : AtomHom dD X Y) : AtomHom dD X Y :=
  Quotient.liftOn f
    (fun f => mk dD X Y (fun a => (dD.algebra a).smul r (f a))) (by
      intro f g hfg
      apply sound
      intro hXY
      change (dD.algebra (Atom.label X)).smul r (f (Atom.label X)) =
        (dD.algebra (Atom.label X)).smul r (g (Atom.label X))
      rw [hfg hXY])

@[simp] theorem coeff_smul {dD : DData} {X Y : Atom} (r : ℝ)
    (f : AtomHom dD X Y) (hXY : Atom.label X = Atom.label Y) :
    (smul r f).coeff hXY =
      (dD.algebra (Atom.label X)).smul r (f.coeff hXY) := by
  induction f using Quotient.inductionOn with
  | _ f => rfl

/-- The identity coefficient family. -/
def id (dD : DData) (X : Atom) : AtomHom dD X X :=
  mk dD X X fun a =>
    if h : Atom.label X = a then
      cast (congrArg (fun b => (dD.algebra b).carrier) h)
        (dD.algebra (Atom.label X)).one
    else
      (dD.algebra a).zero

/-- Put one coefficient at a common endpoint label. -/
def ofLabelEq {dD : DData} {X Y : Atom}
    (_hXY : Atom.label X = Atom.label Y)
    (x : (dD.algebra (Atom.label X)).carrier) : AtomHom dD X Y :=
  mk dD X Y fun a =>
    if h : Atom.label X = a then
      cast (congrArg (fun b => (dD.algebra b).carrier) h) x
    else
      (dD.algebra a).zero

@[simp] theorem coeff_ofLabelEq {dD : DData} {X Y : Atom}
    (hXY : Atom.label X = Atom.label Y)
    (x : (dD.algebra (Atom.label X)).carrier) :
    (ofLabelEq hXY x).coeff hXY = x := by
  unfold ofLabelEq
  rw [coeff_mk]
  simp

@[simp] theorem coeff_id {dD : DData} (X : Atom) :
    (id dD X).coeff rfl = (dD.algebra (Atom.label X)).one := by
  unfold id
  rw [coeff_mk]
  simp

/-- Composition in diagrammatic order.  Coefficients act on the left, so
the coefficient of `f ≫ g` is `g * f`. -/
def comp {dD : DData} {X Y Z : Atom}
    (f : AtomHom dD X Y) (g : AtomHom dD Y Z) : AtomHom dD X Z :=
  if hXY : Atom.label X = Atom.label Y then
    if hYZ : Atom.label Y = Atom.label Z then
      let gAtX : (dD.algebra (Atom.label X)).carrier :=
        cast
          (congrArg (fun a => (dD.algebra a).carrier) hXY).symm
          (g.coeff hYZ)
      ofLabelEq (hXY.trans hYZ)
        ((dD.algebra (Atom.label X)).mul gAtX (f.coeff hXY))
    else
      zero dD X Z
  else
    zero dD X Z

@[simp] theorem coeff_comp {dD : DData} {X Y Z : Atom}
    (f : AtomHom dD X Y) (g : AtomHom dD Y Z)
    (hXY : Atom.label X = Atom.label Y)
    (hYZ : Atom.label Y = Atom.label Z) :
    (comp f g).coeff (hXY.trans hYZ) =
      (dD.algebra (Atom.label X)).mul
        (cast
          (congrArg (fun a => (dD.algebra a).carrier) hXY).symm
          (g.coeff hYZ))
        (f.coeff hXY) := by
  unfold comp
  rw [dif_pos hXY, dif_pos hYZ]
  apply coeff_ofLabelEq

/-- Atoms with a definitionally common label are compared by the single
coefficient at that label.  This specialization keeps equality-proof casts
out of the category-law proofs. -/
theorem ext_same_label {dD : DData} {a : ZMod 8} {r s : ZMod 2}
    {f g : AtomHom dD (a, r) (a, s)}
    (h : f.coeff rfl = g.coeff rfl) : f = g := by
  apply ext
  intro h'
  simpa only [Subsingleton.elim h' rfl] using h

/-- Composition at a definitionally common label is ordinary multiplication
of the two stored coefficients, in diagrammatic order. -/
@[simp] theorem coeff_comp_same_label {dD : DData} {a : ZMod 8}
    {r s t : ZMod 2} (f : AtomHom dD (a, r) (a, s))
    (g : AtomHom dD (a, s) (a, t)) :
    (comp f g).coeff rfl =
      (dD.algebra a).mul (g.coeff rfl) (f.coeff rfl) := by
  simp [Atom.label]

theorem comp_eq_zero_of_left_label_ne {dD : DData} {X Y Z : Atom}
    (hXY : Atom.label X ≠ Atom.label Y)
    (f : AtomHom dD X Y) (g : AtomHom dD Y Z) :
    comp f g = zero dD X Z := by
  simp [comp, hXY]

theorem comp_eq_zero_of_right_label_ne {dD : DData} {X Y Z : Atom}
    (hYZ : Atom.label Y ≠ Atom.label Z)
    (f : AtomHom dD X Y) (g : AtomHom dD Y Z) :
    comp f g = zero dD X Z := by
  by_cases hXY : Atom.label X = Atom.label Y
  · simp [comp, hXY, hYZ]
  · simp [comp, hXY]

/-- Projection to one categorical parity. -/
def component {dD : DData} {X Y : Atom} (i : ZMod 2)
    (f : AtomHom dD X Y) : AtomHom dD X Y :=
  Quotient.liftOn f
    (fun f => mk dD X Y fun a =>
      (dD.algebra a).component
        (i + Atom.shift X + Atom.shift Y) (f a)) (by
      intro f g hfg
      apply sound
      intro hXY
      change (dD.algebra (Atom.label X)).component
          (i + Atom.shift X + Atom.shift Y) (f (Atom.label X)) =
        (dD.algebra (Atom.label X)).component
          (i + Atom.shift X + Atom.shift Y) (g (Atom.label X))
      rw [hfg hXY])

@[simp] theorem coeff_component {dD : DData} {X Y : Atom}
    (i : ZMod 2) (f : AtomHom dD X Y)
    (hXY : Atom.label X = Atom.label Y) :
    (component i f).coeff hXY =
      (dD.algebra (Atom.label X)).component
        (i + Atom.shift X + Atom.shift Y) (f.coeff hXY) := by
  induction f using Quotient.inductionOn with
  | _ f => rfl

/-- Atomic homogeneity, including both endpoint parity shifts. -/
def MemGrade {dD : DData} {X Y : Atom} (i : ZMod 2)
    (f : AtomHom dD X Y) : Prop :=
  ∀ hXY : Atom.label X = Atom.label Y,
    (dD.algebra (Atom.label X)).MemGrade
      (i + Atom.shift X + Atom.shift Y) (f.coeff hXY)

/-- Atomic homogeneity is equivalent to being fixed by the corresponding
stored projection. -/
theorem component_eq_iff_memGrade {dD : DData} {X Y : Atom} (i : ZMod 2)
    (f : AtomHom dD X Y) : component i f = f ↔ MemGrade i f := by
  constructor
  · intro hf hXY
    have hcoeff := congrArg (fun q => q.coeff hXY) hf
    simpa only [coeff_component, SuperAlgebraData.MemGrade] using hcoeff
  · intro hf
    apply ext
    intro hXY
    simpa only [coeff_component, SuperAlgebraData.MemGrade] using hf hXY

/-- Fixed-order finite addition using only stored raw operations. -/
def finSum {dD : DData} {X Y : Atom} :
    (n : ℕ) → (Fin n → AtomHom dD X Y) → AtomHom dD X Y
  | 0, _ => zero dD X Y
  | n + 1, f =>
      add (finSum n (fun i => f i.castSucc)) (f (Fin.last n))

/-- Fixed-order summation respects pointwise equality of coefficient
families. -/
theorem finSum_congr {dD : DData} {X Y : Atom} {n : ℕ}
    {f g : Fin n → AtomHom dD X Y} (h : ∀ i, f i = g i) :
    finSum n f = finSum n g := by
  apply congrArg (fun q => finSum n q)
  funext i
  exact h i

end AtomHom

/-! ## Finite matrices -/

/-- A finite matrix of proof-free atomic morphisms. -/
abbrev Hom (dD : DData) (X Y : Obj) :=
  ∀ i : Fin X.size, ∀ j : Fin Y.size,
    AtomHom dD (X.atom i) (Y.atom j)

namespace Hom

/-- Two finite morphism matrices are equal when all entries agree. -/
@[ext] theorem ext {dD : DData} {X Y : Obj} {f g : Hom dD X Y}
    (h : ∀ i j, f i j = g i j) : f = g := by
  funext i j
  exact h i j

def zero (dD : DData) (X Y : Obj) : Hom dD X Y :=
  fun i j => AtomHom.zero dD (X.atom i) (Y.atom j)

def add {dD : DData} {X Y : Obj} (f g : Hom dD X Y) : Hom dD X Y :=
  fun i j => AtomHom.add (f i j) (g i j)

def neg {dD : DData} {X Y : Obj} (f : Hom dD X Y) : Hom dD X Y :=
  fun i j => AtomHom.neg (f i j)

def smul {dD : DData} {X Y : Obj} (r : ℝ)
    (f : Hom dD X Y) : Hom dD X Y :=
  fun i j => AtomHom.smul r (f i j)

def id (dD : DData) (X : Obj) : Hom dD X X :=
  fun i j =>
    if h : i = j then h ▸ AtomHom.id dD (X.atom i)
    else AtomHom.zero dD (X.atom i) (X.atom j)

def comp {dD : DData} {X Y Z : Obj}
    (f : Hom dD X Y) (g : Hom dD Y Z) : Hom dD X Z :=
  fun i k => AtomHom.finSum Y.size fun j => AtomHom.comp (f i j) (g j k)

def component {dD : DData} {X Y : Obj} (i : ZMod 2)
    (f : Hom dD X Y) : Hom dD X Y :=
  fun r s => AtomHom.component i (f r s)

def MemGrade {dD : DData} {X Y : Obj} (i : ZMod 2)
    (f : Hom dD X Y) : Prop :=
  ∀ r s, AtomHom.MemGrade i (f r s)

/-- Matrix homogeneity is equivalently the fixed-point condition for the
entrywise projection. -/
theorem component_eq_iff_memGrade {dD : DData} {X Y : Obj} (i : ZMod 2)
    (f : Hom dD X Y) : component i f = f ↔ MemGrade i f := by
  constructor
  · intro hf r s
    have hentry := congrFun (congrFun hf r) s
    exact (AtomHom.component_eq_iff_memGrade i (f r s)).mp hentry
  · intro hf
    apply ext
    intro r s
    exact (AtomHom.component_eq_iff_memGrade i (f r s)).mpr (hf r s)

end Hom

end Superfusion.RMod.FromRawDCT
