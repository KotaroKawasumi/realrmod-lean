/-
Superfusion / GaugeChi / TDictGaugeNative

**The `hsz`-free, native-frame variant of the whole `gtOfT` chain.**

`GaugeChi/TDictGauge.lean`'s `gtOfT` and `gtOfT_mem_interSpace` carry the
standing hypothesis

  `hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c`,

inherited from `ColumnDictGauge`'s aligned dictionary `gbrColumnEquiv`.  At
`realGauge` that hypothesis is **false at 12 of the 512 triples** — `(x,4,4)`
and `(4,4,x)` for `x ∈ {1,2,3,5,6,7}`, where `gaugeSizeL = (2,2)` but
`gaugeSizeR = (4,0)` (`docs/route-layer-design.md` §1.5).  The cause is
forced, not a gauge choice: `realSize 4 4 = (4,0)` because `ℍ ᵍ⊗ ℍ` is purely
even, so no `2|2` frame for it exists.  The fix must therefore be structural.

**The structural fix is to stop aligning frames at all.**  `ColumnDictGauge`
already provides a HYPOTHESIS-FREE right dictionary at the right route's own
frame, `gbrNativeColumnEquiv : GBR ≃ₗ[K] FusionColumn (Γ.gaugeRouteR a b c)`,
and `TDictGauge` already proves it is a module map, hypothesis-free
(`gbrNativeColumnEquiv_gtensor_smul`).  What was missing is the `T`-layer at
that frame.  This file supplies it.

## The shape of `T` in the native frame

The two column types differ in BOTH data:

| | index | coefficients |
|---|---|---|
| `FusionColumn (Γ.gaugeRouteL a b c)` | `Fin σL.1 ⊕ Fin σL.2` | `D_{(a+b)+c}` |
| `FusionColumn (Γ.gaugeRouteR a b c)` | `Fin σR.1 ⊕ Fin σR.2` | `D_{a+(b+c)}` |

so `T` is a **rectangular** matrix `R-index × L-index` over `D_{a+(b+c)}`, and
the coefficient cast `κ := Γ.gaugeCast (add_assoc a b c) : D_{(a+b)+c} ≅
D_{a+(b+c)}` is applied to the incoming column *before* multiplying:

  `gmulVecMapNative T v = T *ᵥ (κ ∘ v)`.

Two remarks on why this is the right normalization.

* The cast direction is forced by `gbrNativeColumnEquiv`: `gbrColumnEquiv`
  post-composes with `κ⁻¹` (`ColumnDictGauge`'s `piCongrRight` step uses
  `Γ.gaugeCast (add_assoc a b c).symm`), so the native dictionary sees the
  `κ`-image of everything the aligned one sees — see §6.
* Right-semilinearity along `κ` (condition 5 of `gInterSpace`) is now
  *literally* where the cast lives: `gmulVecMapNative T (op t • v) =
  op (κ t) • gmulVecMapNative T v`, which is exactly `GBR`'s recast right
  action.  In the aligned device that fact was hidden inside
  `gbrColumnEquiv_rightEquiv`.

The left route is read in the right route's coefficient frame by
`gaugeRouteLNative := gaugeRouteL ⬝ gaugeMatrixCast (add_assoc a b c) rfl`,
whose entries are `κ (routeL y i j)` (`gaugeRouteLNative_entry`).  With that,
the intertwining hypothesis is a well-typed identity of `R × L` matrices over
`D_{a+(b+c)}`:

  `routeR(y) * T = sgn(|y|·e) • (T * routeLNative(y))`.

**The rectangular grading of `T`** cannot reuse `matrixSuper`'s grading (which
needs one index type and one mask), so it is spelled out as `rectGradingA`:
entry `(r,s) ∈ D_{a+(b+c)}.grading (e + sumParity σR r + sumParity σL s)`.

## Contents

§1. `rectIntertwinerSubalgebra` + `rectIntertwine_graded_of_adjoin` — the
   rectangular analogue of `RouteMatrixProto`'s §1–§2.  `RouteMatrixProto`'s
   own `intertwine_graded_of_adjoin` does NOT apply verbatim: it needs both
   algebra maps to land in ONE ring, which is exactly what fails here.  The
   proof is unchanged modulo `Matrix.mul_assoc`/`Matrix.mul_smul` replacing
   `mul_assoc`/`mul_smul_comm`; `signTwist` absorbs the Koszul sign as before.

§2. `rectGradingA` — the two-mask entry grading.

§3. Generic `mulVec` helpers (`map_mulVec_apply`, `mulVec_mul_right`).

§4. `gaugeRouteLNative`, `NativeT`, `nativeGrading`, `gmulVecMapNative` and
   its five lemmas (`_apply`, `_rightSemilinear`, `_mem_grading`,
   `_slot_equivariant`, `_bijective`).

§5. `gtOfTNative` and the five `gInterSpace` conditions, assembled in
   `gtOfTNative_mem_interSpace`; plus `gtOfTNative_ne_zero`,
   `gtOfTNative_bijective`.

§6. The generator reduction: `hT_intNative_of_slot_generators` and
   `gtOfTNative_mem_interSpace_of_slot_generators`, drop-in replacements for
   `RouteMatrixProto`'s versions with no `hsz`.

§7. **`gtOfT_eq_gtOfTNative`**: when `hsz` DOES hold, the aligned device is a
   special case of the native one — `gtOfT hsz T = gtOfTNative (alignT hsz T)`
   for the explicit reindex/cast `alignT`, with the grading and intertwining
   hypotheses transported (`alignT_mem_nativeGrading`, `alignT_intertwine`),
   culminating in `gtOfT_mem_interSpace_via_native`.  So the 512-point rollout
   can use ONE uniform device.

No `sorry`, no `native_decide`, no new axioms.
-/
import Superfusion.GaugeChi.RouteMatrixProto

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open scoped Matrix
open Bimod
open GradedTensorProduct

universe u v

/-! ### 1. The rectangular intertwiner subalgebra and its generator reduction

`RouteMatrixProto`'s §1–§2 are stated for two algebra maps into a COMMON ring
`M` and a `T : M`.  In the native frame the two routes land in
`Matrix R R D` and `Matrix L L D` — different rings — and `T : Matrix R L D`
is a rectangular intertwiner between them.  Everything goes through
unchanged: rectangular matrix multiplication is associative
(`Matrix.mul_assoc`), distributive, and commutes with scalars
(`Matrix.mul_smul`), which is all the argument ever used. -/

section RectGen

variable {K : Type*} [CommRing K]
variable {A : Type*} [Ring A] [Algebra K A]
variable {D : Type*} [Ring D] [Algebra K D]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- **The rectangular intertwiner subalgebra**: for algebra maps
`ΦR : A →ₐ[K] Matrix m m D`, `ΦL : A →ₐ[K] Matrix n n D` and a rectangular
`T : Matrix m n D`, the set of `y` with `ΦR y * T = T * ΦL y` is a
`K`-subalgebra of `A`.

Closure under multiplication is the whole content:
`ΦR(yz)·T = ΦR y·(ΦR z·T) = ΦR y·T·ΦL z = T·ΦL y·ΦL z = T·ΦL(yz)`. -/
def rectIntertwinerSubalgebra (ΦR : A →ₐ[K] Matrix m m D) (ΦL : A →ₐ[K] Matrix n n D)
    (T : Matrix m n D) : Subalgebra K A where
  carrier := {y | ΦR y * T = T * ΦL y}
  mul_mem' := by
    intro x y hx hy
    have hx' : ΦR x * T = T * ΦL x := hx
    have hy' : ΦR y * T = T * ΦL y := hy
    show ΦR (x * y) * T = T * ΦL (x * y)
    calc ΦR (x * y) * T = ΦR x * (ΦR y * T) := by rw [map_mul, Matrix.mul_assoc]
      _ = ΦR x * (T * ΦL y) := by rw [hy']
      _ = ΦR x * T * ΦL y := (Matrix.mul_assoc _ _ _).symm
      _ = T * ΦL x * ΦL y := by rw [hx']
      _ = T * ΦL (x * y) := by rw [map_mul, Matrix.mul_assoc]
  one_mem' := by
    show ΦR 1 * T = T * ΦL 1
    rw [map_one, map_one, Matrix.one_mul, Matrix.mul_one]
  add_mem' := by
    intro x y hx hy
    have hx' : ΦR x * T = T * ΦL x := hx
    have hy' : ΦR y * T = T * ΦL y := hy
    show ΦR (x + y) * T = T * ΦL (x + y)
    rw [map_add, map_add, Matrix.add_mul, Matrix.mul_add, hx', hy']
  zero_mem' := by
    show ΦR 0 * T = T * ΦL 0
    rw [map_zero, map_zero, Matrix.zero_mul, Matrix.mul_zero]
  algebraMap_mem' := by
    intro r
    show ΦR (algebraMap K A r) * T = T * ΦL (algebraMap K A r)
    rw [AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]

@[simp] theorem mem_rectIntertwinerSubalgebra {ΦR : A →ₐ[K] Matrix m m D}
    {ΦL : A →ₐ[K] Matrix n n D} {T : Matrix m n D} {y : A} :
    y ∈ rectIntertwinerSubalgebra ΦR ΦL T ↔ ΦR y * T = T * ΦL y := Iff.rfl

/-- **Generators suffice** (the sign-free rectangular form). -/
theorem forall_rectIntertwine_of_adjoin_eq_top (ΦR : A →ₐ[K] Matrix m m D)
    (ΦL : A →ₐ[K] Matrix n n D) (T : Matrix m n D) {S : Set A}
    (hS : Algebra.adjoin K S = ⊤) (hgen : ∀ y ∈ S, ΦR y * T = T * ΦL y) (y : A) :
    ΦR y * T = T * ΦL y := by
  have h : Algebra.adjoin K S ≤ rectIntertwinerSubalgebra ΦR ΦL T :=
    Algebra.adjoin_le fun z hz => hgen z hz
  rw [hS] at h
  exact h Algebra.mem_top

/-- **THE GENERATOR REDUCTION, rectangular form** (the native-frame analogue
of `RouteMatrixProto.intertwine_graded_of_adjoin`): if, on a set `S` of
algebra generators of `A`, every element is homogeneous and satisfies the
signed intertwining identity, then *every* homogeneous element does.

The sign is absorbed by `RouteMatrixProto.signTwist 𝒜 e` exactly as in the
square case; the generator hypothesis bundles homogeneity with the identity,
because that is the shape certificate data has. -/
theorem rectIntertwine_graded_of_adjoin (𝒜 : ZMod 2 → Submodule K A) [GradedAlgebra 𝒜]
    (ΦR : A →ₐ[K] Matrix m m D) (ΦL : A →ₐ[K] Matrix n n D) (T : Matrix m n D)
    (e : ZMod 2) {S : Set A} (hS : Algebra.adjoin K S = ⊤)
    (hgen : ∀ y ∈ S, ∃ j : ZMod 2, y ∈ 𝒜 j ∧
      ΦR y * T = ((sgn (j * e) : ℤˣ) : ℤ) • (T * ΦL y))
    ⦃j : ZMod 2⦄ ⦃y : A⦄ (hy : y ∈ 𝒜 j) :
    ΦR y * T = ((sgn (j * e) : ℤˣ) : ℤ) • (T * ΦL y) := by
  have key : ∀ z : A, ΦR z * T = T * (ΦL.comp (signTwist 𝒜 e)) z := by
    refine forall_rectIntertwine_of_adjoin_eq_top ΦR (ΦL.comp (signTwist 𝒜 e)) T hS ?_
    intro z hz
    obtain ⟨i, hi, hz'⟩ := hgen z hz
    rw [AlgHom.comp_apply, signTwist_of_mem 𝒜 e hi, map_zsmul, Matrix.mul_smul, hz']
  have h := key y
  rwa [AlgHom.comp_apply, signTwist_of_mem 𝒜 e hy, map_zsmul, Matrix.mul_smul] at h

end RectGen

/-! ### 2. The rectangular entry grading

`matrixSuper`'s grading (`matrixGradingA`) is stated for a square matrix over
ONE index type with ONE parity mask.  In the native frame the row and column
index types differ, so the grading is respelled with two masks. -/

section RectGrading

variable {K : Type*} [CommRing K]
variable {D : Type*} [Ring D] [Algebra K D]
variable {m n : Type*}

/-- **The two-mask entry grading** on rectangular matrices: a degree-`i`
matrix has its `(r,s)` entry in `𝒟 (i + πm r + πn s)`.  This is the exact
analogue of `matrixGradingA` for a rectangular shape. -/
def rectGradingA (πm : m → ZMod 2) (πn : n → ZMod 2) (𝒟 : ZMod 2 → Submodule K D)
    (i : ZMod 2) : Submodule K (Matrix m n D) where
  carrier := {M | ∀ r s, M r s ∈ 𝒟 (i + πm r + πn s)}
  zero_mem' _ _ := zero_mem _
  add_mem' {M N} hM hN r s := by
    rw [Matrix.add_apply]
    exact add_mem (hM r s) (hN r s)
  smul_mem' k M hM r s := by
    rw [Matrix.smul_apply]
    exact Submodule.smul_mem _ _ (hM r s)

theorem mem_rectGradingA {πm : m → ZMod 2} {πn : n → ZMod 2}
    {𝒟 : ZMod 2 → Submodule K D} {i : ZMod 2} {M : Matrix m n D} :
    M ∈ rectGradingA πm πn 𝒟 i ↔ ∀ r s, M r s ∈ 𝒟 (i + πm r + πn s) :=
  Iff.rfl

end RectGrading

/-! ### 3. Generic `mulVec` helpers -/

section MulVecHelpers

variable {A B : Type*} [Semiring A] [Semiring B] {m n : Type*} [Fintype n]

/-- A ring hom applied to a `mulVec` is the `mulVec` of the mapped matrix
against the mapped vector. -/
theorem map_mulVec_apply {F : Type*} [FunLike F A B] [RingHomClass F A B]
    (f : F) (M : Matrix m n A) (v : n → A) (i : m) :
    f ((M *ᵥ v) i) = ((M.map f) *ᵥ fun j => f (v j)) i := by
  show f (∑ j, M i j * v j) = ∑ j, (M.map f) i j * f (v j)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => map_mul f _ _

/-- `mulVec` commutes with the right multiplication action on the vector. -/
theorem mulVec_mul_right (M : Matrix m n B) (w : n → B) (d : B) (i : m) :
    (M *ᵥ fun j => w j * d) i = (M *ᵥ w) i * d := by
  show (∑ j, M i j * (w j * d)) = (∑ j, M i j * w j) * d
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end MulVecHelpers

/-! ### 4. The native frame: the recast left route and `gmulVecMapNative` -/

section Native

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

private theorem zmod2_native_shift :
    ∀ e x z j : ZMod 2, e + x + z + (j + z) = j + e + x := by decide +revert

/-- The matrix-frame cast entry formula at a REFLEXIVE size equality (the
only shape this file needs; `TDictGauge`'s general version is private). -/
private theorem gaugeMatrixCast_rfl_entry {x y : G} (h : x = y) {s : ℕ × ℕ}
    (M : ((Γ.D x).matrixSuper s.1 s.2).carrier) (i j : Fin s.1 ⊕ Fin s.2) :
    (Γ.gaugeMatrixCast h (rfl : s = s)).toAlgEquiv M i j
      = (Γ.gaugeCast h).toAlgEquiv (M i j) := by
  subst h
  rfl

/-- **The left route read in the RIGHT route's coefficient frame**: the same
matrix size `gaugeSizeL`, but coefficients transported from `D_{(a+b)+c}` to
`D_{a+(b+c)}` along `Γ.gaugeCast (add_assoc a b c)`.  This is the object the
native intertwining identity multiplies `T` against on the right; unlike
`gaugeRouteR'` it involves NO frame alignment and hence no `hsz`. -/
noncomputable def gaugeRouteLNative :
    SuperAlgEquiv (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c))
      ((Γ.D (a + (b + c))).matrixSuper (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2) :=
  (Γ.gaugeRouteL a b c).trans (Γ.gaugeMatrixCast (add_assoc a b c) rfl)

/-- **The entries of the recast left route** are the `κ`-images of
`gaugeRouteL`'s. -/
theorem gaugeRouteLNative_entry (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier)
    (i j : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    (gaugeRouteLNative K Γ a b c).toAlgEquiv y i j
      = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          ((Γ.gaugeRouteL a b c).toAlgEquiv y i j) :=
  gaugeMatrixCast_rfl_entry K Γ (add_assoc a b c) ((Γ.gaugeRouteL a b c).toAlgEquiv y) i j

/-- The recast left route, entrywise, as a `Matrix.map`. -/
theorem gaugeRouteLNative_apply (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) :
    (gaugeRouteLNative K Γ a b c).toAlgEquiv y
      = ((Γ.gaugeRouteL a b c).toAlgEquiv y).map
          (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv :=
  Matrix.ext fun i j => gaugeRouteLNative_entry K Γ a b c y i j

/-- **The right route's matrix image at the bare `Matrix` spelling.**
`((Γ.D _).matrixSuper p q).carrier` is a structure projection that instance
search does NOT unfold at `instances` transparency, so `*` fails to elaborate
against it; every statement below therefore uses this ascribed form. -/
noncomputable abbrev routeRMat (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) :
    Matrix (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      (Γ.D (a + (b + c))).carrier :=
  (Γ.gaugeRouteR a b c).toAlgEquiv y

/-- The recast left route's matrix image at the bare `Matrix` spelling. -/
noncomputable abbrev routeLNativeMat (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) :
    Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Γ.D (a + (b + c))).carrier :=
  (gaugeRouteLNative K Γ a b c).toAlgEquiv y

/-- **The rectangular shape of a native connector**: rows indexed by the
right route's frame, columns by the left route's, coefficients in the right
route's tower `D_{a+(b+c)}`. -/
abbrev NativeT : Type _ :=
  Matrix (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
    (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) (Γ.D (a + (b + c))).carrier

/-- **The rectangular grading of a native connector**: entry `(r,s)` of a
degree-`e` connector lies in `D_{a+(b+c)}.grading (e + πR r + πL s)`.  This is
the native-frame replacement for `(matrixSuper …).grading e`, which cannot be
used because the row and column index types differ. -/
abbrev nativeGrading (e : ZMod 2) : Submodule K (NativeT K Γ a b c) :=
  rectGradingA (sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2)
    (sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2)
    (Γ.D (a + (b + c))).grading e

theorem mem_nativeGrading {e : ZMod 2} {T : NativeT K Γ a b c} :
    T ∈ nativeGrading K Γ a b c e ↔ ∀ r s, T r s ∈ (Γ.D (a + (b + c))).grading
      (e + sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2 r
        + sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2 s) :=
  Iff.rfl

/-- **The native column-side map of a rectangular matrix element**
`T : Matrix (R-index) (L-index) (D_{a+(b+c)})`: the incoming
`FusionColumn (Γ.gaugeRouteL a b c)` (values in `D_{(a+b)+c}`) is cast into
`D_{a+(b+c)}` entrywise and then multiplied.  **No `hsz`.** -/
noncomputable def gmulVecMapNative (T : NativeT K Γ a b c) :
    FusionColumn (Γ.gaugeRouteL a b c) →ₗ[K] FusionColumn (Γ.gaugeRouteR a b c) where
  toFun v := T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)
  map_add' u v := by
    show T *ᵥ (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv ((u + v) s)) = _
    rw [show (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv ((u + v) s))
        = (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (u s))
          + (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)) from by
      funext s
      exact map_add _ _ _]
    exact Matrix.mulVec_add _ _ _
  map_smul' k v := by
    show T *ᵥ (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv ((k • v) s)) = _
    rw [show (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv ((k • v) s))
        = k • (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)) from by
      funext s
      exact map_smul _ _ _]
    exact Matrix.mulVec_smul _ _ _

theorem gmulVecMapNative_apply (T : NativeT K Γ a b c)
    (v : FusionColumn (Γ.gaugeRouteL a b c)) :
    gmulVecMapNative K Γ a b c T v
      = T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s) := rfl

/-- **`gmulVecMapNative` is right SEMIlinear along `Γ.gaugeCast (add_assoc a
b c)`** — the native-frame replacement for `gmulVecMap_rightEquiv`.  In the
aligned device the coefficient cast was hidden inside `gbrColumnEquiv`; here
it is exactly this lemma, and it is the reason condition 5 of `gInterSpace`
still comes out right without `hsz`. -/
theorem gmulVecMapNative_rightSemilinear (T : NativeT K Γ a b c)
    (t : (Γ.D (a + b + c)).carrier) (v : FusionColumn (Γ.gaugeRouteL a b c)) :
    gmulVecMapNative K Γ a b c T (MulOpposite.op t • v)
      = MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t)
          • gmulVecMapNative K Γ a b c T v := by
  refine funext fun r => ?_
  show (T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s * t)) r
    = (T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s))
        r * (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t
  rw [show (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s * t))
      = (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)
          * (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) from by
    funext s
    exact map_mul _ _ _]
  exact mulVec_mul_right T _ _ r

/-- **`gmulVecMapNative` is graded**: a degree-`e` connector maps the
degree-`j` layer of the left column to the degree-`(j+e)` layer of the native
right column.  The coefficient cast preserves degrees
(`Γ.gaugeCast_mem_grading`) and the two `πL` contributions cancel. -/
theorem gmulVecMapNative_mem_grading {T : NativeT K Γ a b c} {e : ZMod 2}
    (hT : T ∈ nativeGrading K Γ a b c e)
    {j : ZMod 2} {v : FusionColumn (Γ.gaugeRouteL a b c)}
    (hv : v ∈ FusionColumn.grading (Γ.gaugeRouteL a b c) j) :
    gmulVecMapNative K Γ a b c T v
      ∈ FusionColumn.grading (Γ.gaugeRouteR a b c) (j + e) := by
  intro r
  show (T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)) r
    ∈ (Γ.D (a + (b + c))).grading
        (j + e + sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2 r)
  show (∑ s, T r s * (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)) ∈ _
  refine Submodule.sum_mem _ fun s _ => ?_
  have hTrs := hT r s
  have hvs : (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)
      ∈ (Γ.D (a + (b + c))).grading
          (j + sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2 s) :=
    Γ.gaugeCast_mem_grading (add_assoc a b c) (hv s)
  have hmul := SetLike.mul_mem_graded hTrs hvs
  rwa [zmod2_native_shift e
    (sumParity (Γ.gaugeSizeR a b c).1 (Γ.gaugeSizeR a b c).2 r)
    (sumParity (Γ.gaugeSizeL a b c).1 (Γ.gaugeSizeL a b c).2 s) j] at hmul

/-- **`gmulVecMapNative` is slot-equivariant for the FULL triple-tensor
action**, given the native intertwining hypothesis on `T` — the native-frame
replacement for `gmulVecMap_slot_equivariant`.  Note the hypothesis compares
`Γ.gaugeRouteR` (NOT `gaugeRouteR'`) with `gaugeRouteLNative`, so no frame
alignment and no `hsz` occur anywhere. -/
theorem gmulVecMapNative_slot_equivariant (T : NativeT K Γ a b c) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * routeLNativeMat K Γ a b c y))
    {j : ZMod 2} {y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier}
    (hy : y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j)
    (v : FusionColumn (Γ.gaugeRouteL a b c)) :
    gmulVecMapNative K Γ a b c T ((Γ.gaugeRouteL a b c).toAlgEquiv y *ᵥ v)
      = ((sgn (j * e) : ℤˣ) : ℤ) •
          ((Γ.gaugeRouteR a b c).toAlgEquiv y *ᵥ gmulVecMapNative K Γ a b c T v) := by
  set vc : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2
      → (Γ.D (a + (b + c))).carrier :=
    fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s) with hvcdef
  set YN : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Γ.D (a + (b + c))).carrier :=
    (gaugeRouteLNative K Γ a b c).toAlgEquiv y with hYNdef
  set X : Matrix (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      (Γ.D (a + (b + c))).carrier :=
    (Γ.gaugeRouteR a b c).toAlgEquiv y with hXdef
  have hint : X * T = ((sgn (j * e) : ℤˣ) : ℤ) • (T * YN) := hT_int hy
  have hcol : (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        (((Γ.gaugeRouteL a b c).toAlgEquiv y *ᵥ v) s)) = YN *ᵥ vc := by
    funext s
    rw [hYNdef, gaugeRouteLNative_apply]
    exact map_mulVec_apply _ _ _ s
  show T *ᵥ (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
      (((Γ.gaugeRouteL a b c).toAlgEquiv y *ᵥ v) s))
    = ((sgn (j * e) : ℤˣ) : ℤ) • (X *ᵥ (T *ᵥ vc))
  rw [hcol]
  have hcomm : T * YN = ((sgn (j * e) : ℤˣ) : ℤ) • (X * T) := by
    have h1 : ((sgn (j * e) : ℤˣ) : ℤ) • (((sgn (j * e) : ℤˣ) : ℤ) • (T * YN))
        = ((sgn (j * e) : ℤˣ) : ℤ) • (X * T) :=
      congrArg (fun w => ((sgn (j * e) : ℤˣ) : ℤ) • w) hint.symm
    rw [smul_smul,
      show ((sgn (j * e) : ℤˣ) : ℤ) * ((sgn (j * e) : ℤˣ) : ℤ) = 1 from by
        rw [← Units.val_mul, sgn_mul_self', Units.val_one],
      one_smul] at h1
    exact h1
  calc T *ᵥ (YN *ᵥ vc) = (T * YN) *ᵥ vc := Matrix.mulVec_mulVec vc T YN
    _ = (((sgn (j * e) : ℤˣ) : ℤ) • (X * T)) *ᵥ vc := congrArg (· *ᵥ vc) hcomm
    _ = ((sgn (j * e) : ℤˣ) : ℤ) • ((X * T) *ᵥ vc) := Matrix.smul_mulVec _ _ _
    _ = ((sgn (j * e) : ℤˣ) : ℤ) • (X *ᵥ (T *ᵥ vc)) :=
        congrArg (fun w => ((sgn (j * e) : ℤˣ) : ℤ) • w) (Matrix.mulVec_mulVec vc X T).symm

/-- **`gmulVecMapNative` by a two-sidedly invertible rectangular `T` is
bijective**.  `IsUnit T` is not available for a rectangular `T`, so the
inverse is supplied explicitly; at the concrete gauges `S` is the frozen
inverse connector. -/
theorem gmulVecMapNative_bijective (T : NativeT K Γ a b c)
    (S : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      (Γ.D (a + (b + c))).carrier)
    (hTS : T * S = 1) (hST : S * T = 1) :
    Function.Bijective (gmulVecMapNative K Γ a b c T) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun w => fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm ((S *ᵥ w) s), ?_, ?_⟩
  · intro v
    refine funext fun s => ?_
    show (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm
        ((S *ᵥ (T *ᵥ fun s' => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s'))) s) = v s
    rw [Matrix.mulVec_mulVec, hST, Matrix.one_mulVec]
    exact (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm_apply_apply (v s)
  · intro w
    refine funext fun r => ?_
    show (T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm ((S *ᵥ w) s))) r = w r
    rw [show (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm ((S *ᵥ w) s)))
        = S *ᵥ w from by
      funext s
      exact (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.apply_symm_apply _,
      Matrix.mulVec_mulVec, hTS, Matrix.one_mulVec]

/-! ### 5. `gtOfTNative` and the five `gInterSpace` conditions -/

/-- **`gtOfTNative T`**: the native-frame transport of a rectangular matrix
element into a `K`-linear map `GBL → GBR`, through the HYPOTHESIS-FREE column
dictionaries `gblColumnEquiv` and `gbrNativeColumnEquiv`.  The exact analogue
of `TDictGauge.gtOfT`, **without `hsz`**. -/
noncomputable def gtOfTNative (T : NativeT K Γ a b c) :
    GBL Γ a b c →ₗ[K] GBR Γ a b c :=
  (gbrNativeColumnEquiv K Γ a b c).symm.toLinearMap ∘ₗ
    gmulVecMapNative K Γ a b c T ∘ₗ (gblColumnEquiv K Γ a b c).toLinearMap

theorem gtOfTNative_apply (T : NativeT K Γ a b c) (m : GBL Γ a b c) :
    gtOfTNative K Γ a b c T m
      = (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m)) := rfl

/-- **Condition 1 of 5**: `gtOfTNative T` is homogeneous of `T`'s degree. -/
theorem gtOfTNative_mem_homGrading {T : NativeT K Γ a b c} {e : ZMod 2}
    (hT : T ∈ nativeGrading K Γ a b c e) :
    gtOfTNative K Γ a b c T
      ∈ homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c) e := by
  refine (mem_homGrading (GBL.grading Γ a b c) (GBR.grading Γ a b c)).mpr ?_
  intro i m hm
  rw [gtOfTNative_apply]
  exact gbrNativeColumnEquiv_symm_mem_grading K Γ a b c
    (gmulVecMapNative_mem_grading K Γ a b c hT (gblColumnEquiv_mem_grading K Γ a b c hm))

/-- **Condition 2 of 5**: `D_a`-slot super-equivariance. -/
theorem gtOfTNative_mem_superEquivariant_a (T : NativeT K Γ a b c) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * routeLNativeMat K Γ a b c y)) :
    gtOfTNative K Γ a b c T ∈ superEquivariant (Γ.D a).grading e := by
  refine (mem_superEquivariant (Γ.D a).grading).mpr ?_
  intro i x hx m
  obtain ⟨Y, hY⟩ : ∃ Y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier,
      Y = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeLeft (Γ.D a).grading (Γ.D b).grading x) := ⟨_, rfl⟩
  have hembL : Y • m = x • m := GBL.aEmbed K Γ a b c _ x rfl Y hY m
  have hembR : ∀ n : GBR Γ a b c, Y • n = x • n :=
    fun n => GBR.aEmbed_smul K Γ a b c _ x rfl Y hY n
  have hmem : Y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i := by
    rw [hY]
    exact includeLeft_mem_tensorGrading _ _ (includeLeft_mem_tensorGrading _ _ hx)
  calc gtOfTNative K Γ a b c T (x • m)
      = (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T
            ((Γ.gaugeRouteL a b c).toAlgEquiv Y *ᵥ gblColumnEquiv K Γ a b c m)) := by
        rw [gtOfTNative_apply, ← hembL, gblColumnEquiv_gtensor_smul]
    _ = (gbrNativeColumnEquiv K Γ a b c).symm
          (((sgn (i * e) : ℤˣ) : ℤ) •
            ((Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ
              gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m))) := by
        rw [gmulVecMapNative_slot_equivariant K Γ a b c T hT_int hmem]
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (gbrNativeColumnEquiv K Γ a b c).symm
          ((Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ
            gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m)) :=
        map_zsmul (gbrNativeColumnEquiv K Γ a b c).symm _ _
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (Y • (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m))) :=
        congrArg (fun w => ((sgn (i * e) : ℤˣ) : ℤ) • w)
          (conjSymm (gbrNativeColumnEquiv K Γ a b c) (fun n => Y • n)
            (fun w => (Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ w)
            (gbrNativeColumnEquiv_gtensor_smul K Γ a b c Y) _)
    _ = ((sgn (e * i) : ℤˣ) : ℤ) • (x • gtOfTNative K Γ a b c T m) := by
        rw [hembR, mul_comm i e]
        rfl

/-- **Condition 3 of 5**: `D_b`-slot super-equivariance. -/
theorem gtOfTNative_mem_superEquivariant_b (T : NativeT K Γ a b c) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * routeLNativeMat K Γ a b c y)) :
    gtOfTNative K Γ a b c T ∈ superEquivariant (Γ.D b).grading e := by
  refine (mem_superEquivariant (Γ.D b).grading).mpr ?_
  intro i y hy m
  obtain ⟨Y, hY⟩ : ∃ Y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier,
      Y = GradedTensorProduct.includeLeft ((Γ.D a).gtensor (Γ.D b)).grading (Γ.D c).grading
        (GradedTensorProduct.includeRight (Γ.D a).grading (Γ.D b).grading y) := ⟨_, rfl⟩
  have hembL : Y • m = y • m := GBL.bEmbed K Γ a b c _ y rfl Y hY m
  have hembR : ∀ n : GBR Γ a b c, Y • n = y • n :=
    fun n => GBR.bEmbed_smul K Γ a b c _ y rfl Y hY n
  have hmem : Y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i := by
    rw [hY]
    exact includeLeft_mem_tensorGrading _ _ (includeRight_mem_tensorGrading _ _ hy)
  calc gtOfTNative K Γ a b c T (y • m)
      = (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T
            ((Γ.gaugeRouteL a b c).toAlgEquiv Y *ᵥ gblColumnEquiv K Γ a b c m)) := by
        rw [gtOfTNative_apply, ← hembL, gblColumnEquiv_gtensor_smul]
    _ = (gbrNativeColumnEquiv K Γ a b c).symm
          (((sgn (i * e) : ℤˣ) : ℤ) •
            ((Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ
              gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m))) := by
        rw [gmulVecMapNative_slot_equivariant K Γ a b c T hT_int hmem]
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (gbrNativeColumnEquiv K Γ a b c).symm
          ((Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ
            gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m)) :=
        map_zsmul (gbrNativeColumnEquiv K Γ a b c).symm _ _
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (Y • (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m))) :=
        congrArg (fun w => ((sgn (i * e) : ℤˣ) : ℤ) • w)
          (conjSymm (gbrNativeColumnEquiv K Γ a b c) (fun n => Y • n)
            (fun w => (Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ w)
            (gbrNativeColumnEquiv_gtensor_smul K Γ a b c Y) _)
    _ = ((sgn (e * i) : ℤˣ) : ℤ) • (y • gtOfTNative K Γ a b c T m) := by
        rw [hembR, mul_comm i e]
        rfl

/-- **Condition 4 of 5**: `D_c`-slot super-equivariance. -/
theorem gtOfTNative_mem_superEquivariant_c (T : NativeT K Γ a b c) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * routeLNativeMat K Γ a b c y)) :
    gtOfTNative K Γ a b c T ∈ superEquivariant (Γ.D c).grading e := by
  refine (mem_superEquivariant (Γ.D c).grading).mpr ?_
  intro i z hz m
  obtain ⟨Y, hY⟩ : ∃ Y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier,
      Y = GradedTensorProduct.includeRight ((Γ.D a).gtensor (Γ.D b)).grading
        (Γ.D c).grading z := ⟨_, rfl⟩
  have hembL : Y • m = z • m := GBL.cEmbed K Γ a b c Y z hY m
  have hembR : ∀ n : GBR Γ a b c, Y • n = z • n := fun n => GBR.cEmbed_smul K Γ a b c Y z hY n
  have hmem : Y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading i := by
    rw [hY]
    exact includeRight_mem_tensorGrading _ _ hz
  calc gtOfTNative K Γ a b c T (z • m)
      = (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T
            ((Γ.gaugeRouteL a b c).toAlgEquiv Y *ᵥ gblColumnEquiv K Γ a b c m)) := by
        rw [gtOfTNative_apply, ← hembL, gblColumnEquiv_gtensor_smul]
    _ = (gbrNativeColumnEquiv K Γ a b c).symm
          (((sgn (i * e) : ℤˣ) : ℤ) •
            ((Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ
              gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m))) := by
        rw [gmulVecMapNative_slot_equivariant K Γ a b c T hT_int hmem]
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (gbrNativeColumnEquiv K Γ a b c).symm
          ((Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ
            gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m)) :=
        map_zsmul (gbrNativeColumnEquiv K Γ a b c).symm _ _
    _ = ((sgn (i * e) : ℤˣ) : ℤ) • (Y • (gbrNativeColumnEquiv K Γ a b c).symm
          (gmulVecMapNative K Γ a b c T (gblColumnEquiv K Γ a b c m))) :=
        congrArg (fun w => ((sgn (i * e) : ℤˣ) : ℤ) • w)
          (conjSymm (gbrNativeColumnEquiv K Γ a b c) (fun n => Y • n)
            (fun w => (Γ.gaugeRouteR a b c).toAlgEquiv Y *ᵥ w)
            (gbrNativeColumnEquiv_gtensor_smul K Γ a b c Y) _)
    _ = ((sgn (e * i) : ℤˣ) : ℤ) • (z • gtOfTNative K Γ a b c T m) := by
        rw [hembR, mul_comm i e]
        rfl

/-- **Condition 5 of 5**: right-semilinearity along `Γ.gaugeCast (add_assoc a
b c)`.  Here the coefficient cast that the aligned device hid inside
`gbrColumnEquiv` is carried by `gmulVecMapNative_rightSemilinear`, and the
native dictionary contributes only its PLAIN right equivariance. -/
theorem gtOfTNative_mem_rightSemilinear (T : NativeT K Γ a b c) :
    gtOfTNative K Γ a b c T
      ∈ rightSemilinear
          ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.toAlgHom.toRingHom) := by
  intro t m
  rw [gtOfTNative_apply, gtOfTNative_apply, gblColumnEquiv_rightEquiv,
    gmulVecMapNative_rightSemilinear,
    conjSymm (gbrNativeColumnEquiv K Γ a b c)
      (fun n => MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) • n)
      (fun w => MulOpposite.op ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t) • w)
      (gbrNativeColumnEquiv_rightEquiv K Γ a b c
        ((Γ.gaugeCast (add_assoc a b c)).toAlgEquiv t))]
  rfl

/-- **`gtOfTNative T ∈ gInterSpace K Γ a b c e`** (all five conditions),
**with NO size hypothesis** — the native-frame replacement for
`TDictGauge.gtOfT_mem_interSpace`, available at all 512 `realGauge` triples
including the 12 where `hsz` fails. -/
theorem gtOfTNative_mem_interSpace {T : NativeT K Γ a b c} {e : ZMod 2}
    (hT : T ∈ nativeGrading K Γ a b c e)
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * routeLNativeMat K Γ a b c y)) :
    gtOfTNative K Γ a b c T ∈ gInterSpace K Γ a b c e := by
  rw [mem_gInterSpace_iff]
  exact ⟨gtOfTNative_mem_homGrading K Γ a b c hT,
    gtOfTNative_mem_superEquivariant_a K Γ a b c T hT_int,
    gtOfTNative_mem_superEquivariant_b K Γ a b c T hT_int,
    gtOfTNative_mem_superEquivariant_c K Γ a b c T hT_int,
    gtOfTNative_mem_rightSemilinear K Γ a b c T⟩

/-- **A nonzero `T` gives a nonzero intertwiner.**  Both column dictionaries
are equivalences and the coefficient cast is a bijection, so `mulVec` by `T`
still recovers `T`'s columns at the standard basis vectors. -/
theorem gtOfTNative_ne_zero {T : NativeT K Γ a b c} (hT : T ≠ 0) :
    gtOfTNative K Γ a b c T ≠ 0 := by
  intro h0
  refine hT ?_
  have hmv : ∀ w : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2
      → (Γ.D (a + (b + c))).carrier, T *ᵥ w = 0 := by
    intro w
    set v : FusionColumn (Γ.gaugeRouteL a b c) :=
      fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.symm (w s) with hvdef
    have h1 : gtOfTNative K Γ a b c T ((gblColumnEquiv K Γ a b c).symm v) = 0 := by
      rw [h0]; rfl
    rw [gtOfTNative_apply, LinearEquiv.apply_symm_apply] at h1
    have h2 := congrArg (gbrNativeColumnEquiv K Γ a b c) h1
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    have h3 : (T *ᵥ fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)) = 0 := h2
    rwa [show (fun s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (v s)) = w from by
      funext s
      exact (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv.apply_symm_apply (w s)] at h3
  refine Matrix.ext_of_mulVec_single ?_
  intro s
  exact (hmv (Pi.single s 1)).trans (Matrix.zero_mulVec _).symm

/-- **`gtOfTNative T` is bijective** when `T` has a two-sided inverse: the
composite of the three bijections `gblColumnEquiv`, `gmulVecMapNative T`,
`gbrNativeColumnEquiv.symm`. -/
theorem gtOfTNative_bijective (T : NativeT K Γ a b c)
    (S : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
      (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
      (Γ.D (a + (b + c))).carrier)
    (hTS : T * S = 1) (hST : S * T = 1) :
    Function.Bijective (gtOfTNative K Γ a b c T) := by
  have hcomp : (gtOfTNative K Γ a b c T : GBL Γ a b c → GBR Γ a b c)
      = (gbrNativeColumnEquiv K Γ a b c).symm ∘ (gmulVecMapNative K Γ a b c T)
        ∘ (gblColumnEquiv K Γ a b c) := rfl
  rw [hcomp]
  exact (gbrNativeColumnEquiv K Γ a b c).symm.bijective.comp
    ((gmulVecMapNative_bijective K Γ a b c T S hTS hST).comp
      (gblColumnEquiv K Γ a b c).bijective)

/-! ### 6. The generator reduction at the native frame

`RouteMatrixProto`'s §4 consumer lemmas, restated without `hsz`.  The three
slot embeddings (`aSlot`/`bSlot`/`cSlot`), their grading anchors and
`adjoin_slots_eq_top` are reused verbatim — only the two algebra maps change,
from `(gaugeRouteR', gaugeRouteL)` into one matrix ring to
`(gaugeRouteR, gaugeRouteLNative)` into two. -/

/-- The right route as an `AlgHom` into the bare `Matrix` spelling. -/
noncomputable def routeRAlgHom :
    (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier →ₐ[K]
      Matrix (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
        (Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
        (Γ.D (a + (b + c))).carrier :=
  (Γ.gaugeRouteR a b c).toAlgEquiv.toAlgHom

theorem routeRAlgHom_apply (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) :
    routeRAlgHom K Γ a b c y = routeRMat K Γ a b c y := rfl

/-- The recast left route as an `AlgHom` into the bare `Matrix` spelling. -/
noncomputable def routeLNativeAlgHom :
    (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier →ₐ[K]
      Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
        (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
        (Γ.D (a + (b + c))).carrier :=
  (gaugeRouteLNative K Γ a b c).toAlgEquiv.toAlgHom

theorem routeLNativeAlgHom_apply (y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier) :
    routeLNativeAlgHom K Γ a b c y = routeLNativeMat K Γ a b c y := rfl

/-- **The native intertwining hypothesis from slot generators**: the
`∀`-quantified hypothesis of `gtOfTNative_mem_interSpace` follows from its
restriction to homogeneous generators of the three factor algebras.  Exact
analogue of `RouteMatrixProto.hT_int_of_slot_generators`, with no `hsz`. -/
theorem hT_intNative_of_slot_generators (T : NativeT K Γ a b c) (e : ZMod 2)
    {ιA ιB ιC : Type*}
    (gA : ιA → (Γ.D a).carrier) (dA : ιA → ZMod 2)
    (gB : ιB → (Γ.D b).carrier) (dB : ιB → ZMod 2)
    (gC : ιC → (Γ.D c).carrier) (dC : ιC → ZMod 2)
    (hAmem : ∀ t, gA t ∈ (Γ.D a).grading (dA t))
    (hBmem : ∀ t, gB t ∈ (Γ.D b).grading (dB t))
    (hCmem : ∀ t, gC t ∈ (Γ.D c).grading (dC t))
    (hAtop : Algebra.adjoin K (Set.range gA) = ⊤)
    (hBtop : Algebra.adjoin K (Set.range gB) = ⊤)
    (hCtop : Algebra.adjoin K (Set.range gC) = ⊤)
    (hAint : ∀ t, routeRMat K Γ a b c (aSlot K Γ a b c (gA t)) * T
      = ((sgn (dA t * e) : ℤˣ) : ℤ) •
          (T * routeLNativeMat K Γ a b c (aSlot K Γ a b c (gA t))))
    (hBint : ∀ t, routeRMat K Γ a b c (bSlot K Γ a b c (gB t)) * T
      = ((sgn (dB t * e) : ℤˣ) : ℤ) •
          (T * routeLNativeMat K Γ a b c (bSlot K Γ a b c (gB t))))
    (hCint : ∀ t, routeRMat K Γ a b c (cSlot K Γ a b c (gC t)) * T
      = ((sgn (dC t * e) : ℤˣ) : ℤ) •
          (T * routeLNativeMat K Γ a b c (cSlot K Γ a b c (gC t)))) :
    ∀ ⦃j : ZMod 2⦄ ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * routeLNativeMat K Γ a b c y) := by
  refine rectIntertwine_graded_of_adjoin (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading
    (routeRAlgHom K Γ a b c) (routeLNativeAlgHom K Γ a b c) T e
    (adjoin_slots_eq_top K Γ a b c hAtop hBtop hCtop) ?_
  rintro y ((⟨x, ⟨t, rfl⟩, rfl⟩ | ⟨x, ⟨t, rfl⟩, rfl⟩) | ⟨x, ⟨t, rfl⟩, rfl⟩)
  · exact ⟨dA t, aSlot_mem_grading K Γ a b c (hAmem t), hAint t⟩
  · exact ⟨dB t, bSlot_mem_grading K Γ a b c (hBmem t), hBint t⟩
  · exact ⟨dC t, cSlot_mem_grading K Γ a b c (hCmem t), hCint t⟩

/-- **`gtOfTNative T ∈ gInterSpace` from slot generators**: the packaged,
`hsz`-FREE drop-in replacement for
`RouteMatrixProto.gtOfT_mem_interSpace_of_slot_generators`.  Every hypothesis
is finite per triple: a rectangular degree check on `T` and
`dim D_a + dim D_b + dim D_c` matrix identities. -/
theorem gtOfTNative_mem_interSpace_of_slot_generators
    {T : NativeT K Γ a b c} {e : ZMod 2}
    (hT : T ∈ nativeGrading K Γ a b c e)
    {ιA ιB ιC : Type*}
    (gA : ιA → (Γ.D a).carrier) (dA : ιA → ZMod 2)
    (gB : ιB → (Γ.D b).carrier) (dB : ιB → ZMod 2)
    (gC : ιC → (Γ.D c).carrier) (dC : ιC → ZMod 2)
    (hAmem : ∀ t, gA t ∈ (Γ.D a).grading (dA t))
    (hBmem : ∀ t, gB t ∈ (Γ.D b).grading (dB t))
    (hCmem : ∀ t, gC t ∈ (Γ.D c).grading (dC t))
    (hAtop : Algebra.adjoin K (Set.range gA) = ⊤)
    (hBtop : Algebra.adjoin K (Set.range gB) = ⊤)
    (hCtop : Algebra.adjoin K (Set.range gC) = ⊤)
    (hAint : ∀ t, routeRMat K Γ a b c (aSlot K Γ a b c (gA t)) * T
      = ((sgn (dA t * e) : ℤˣ) : ℤ) •
          (T * routeLNativeMat K Γ a b c (aSlot K Γ a b c (gA t))))
    (hBint : ∀ t, routeRMat K Γ a b c (bSlot K Γ a b c (gB t)) * T
      = ((sgn (dB t * e) : ℤˣ) : ℤ) •
          (T * routeLNativeMat K Γ a b c (bSlot K Γ a b c (gB t))))
    (hCint : ∀ t, routeRMat K Γ a b c (cSlot K Γ a b c (gC t)) * T
      = ((sgn (dC t * e) : ℤˣ) : ℤ) •
          (T * routeLNativeMat K Γ a b c (cSlot K Γ a b c (gC t)))) :
    gtOfTNative K Γ a b c T ∈ gInterSpace K Γ a b c e :=
  gtOfTNative_mem_interSpace K Γ a b c hT
    (hT_intNative_of_slot_generators K Γ a b c T e gA dA gB dB gC dC
      hAmem hBmem hCmem hAtop hBtop hCtop hAint hBint hCint)

/-! ### 7. The aligned device is a SPECIAL CASE of the native one

When `hsz` does hold, `TDictGauge.gtOfT` is literally `gtOfTNative` at the
transported connector.  Consequently a 512-point rollout needs only ONE
device: the native one, which exists at all triples. -/

/-- The `κ`-roundtrip: `Γ.gaugeCast (add_assoc a b c)` undoes
`Γ.gaugeCast (add_assoc a b c).symm`. -/
private theorem gaugeCast_assoc_symm_cancel (w : (Γ.D (a + (b + c))).carrier) :
    (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
        ((Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv w) = w := by
  rw [Γ.gaugeCast_trans_apply]
  exact Γ.gaugeCast_refl_apply _ w

/-- **The aligned-to-native transport of a connector**: reindex the rows along
`gaugeSizeCastEquiv hsz` and cast the entries along
`Γ.gaugeCast (add_assoc a b c)`. -/
noncomputable def alignT (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) : NativeT K Γ a b c :=
  Matrix.of fun r s => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
    (T (gaugeSizeCastEquiv K Γ a b c hsz r) s)

theorem alignT_apply (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier)
    (r : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2)
    (s : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2) :
    alignT K Γ a b c hsz T r s
      = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (T (gaugeSizeCastEquiv K Γ a b c hsz r) s) := rfl

/-- **The two right dictionaries agree up to the frame cast**: the native one
is the `κ`-image of the aligned one, read at the `gaugeSizeCastEquiv`-image of
the index. -/
theorem gbrNativeColumnEquiv_eq_gbrColumnEquiv
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c) (n : GBR Γ a b c)
    (r : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2) :
    gbrNativeColumnEquiv K Γ a b c n r
      = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (gbrColumnEquiv K Γ a b c hsz n (gaugeSizeCastEquiv K Γ a b c hsz r)) := by
  have hval : gbrColumnEquiv K Γ a b c hsz n (gaugeSizeCastEquiv K Γ a b c hsz r)
      = (Γ.gaugeCast (add_assoc a b c).symm).toAlgEquiv
          (gbrNativeColumnEquiv K Γ a b c n
            ((gaugeSizeCastEquiv K Γ a b c hsz).symm
              (gaugeSizeCastEquiv K Γ a b c hsz r))) := rfl
  rw [hval, Equiv.symm_apply_apply, gaugeCast_assoc_symm_cancel]

/-- **`gtOfT` IS `gtOfTNative` at the transported connector** (whenever `hsz`
holds).  The aligned device of `TDictGauge` is therefore redundant: the native
device of this file covers it. -/
theorem gtOfT_eq_gtOfTNative (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) :
    gtOfT K Γ a b c hsz T = gtOfTNative K Γ a b c (alignT K Γ a b c hsz T) := by
  refine LinearMap.ext fun m => ?_
  refine (gbrNativeColumnEquiv K Γ a b c).injective ?_
  rw [gtOfTNative_apply, LinearEquiv.apply_symm_apply]
  refine funext fun r => ?_
  rw [gtOfT_apply, gbrNativeColumnEquiv_eq_gbrColumnEquiv K Γ a b c hsz,
    LinearEquiv.apply_symm_apply]
  show (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
      (∑ s, T (gaugeSizeCastEquiv K Γ a b c hsz r) s * gblColumnEquiv K Γ a b c m s)
    = ∑ s, alignT K Γ a b c hsz T r s
        * (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv (gblColumnEquiv K Γ a b c m s)
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, alignT_apply]

/-- The grading hypothesis transports: an aligned degree-`e` connector becomes
a native degree-`e` one (`sumParity_gaugeSizeCastEquiv` matches the two row
masks, `Γ.gaugeCast_mem_grading` the coefficient degrees). -/
theorem alignT_mem_nativeGrading (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier} {e : ZMod 2}
    (hT : T ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).grading e) :
    alignT K Γ a b c hsz T ∈ nativeGrading K Γ a b c e := by
  intro r s
  have h := hT (gaugeSizeCastEquiv K Γ a b c hsz r) s
  rw [sumParity_gaugeSizeCastEquiv K Γ a b c hsz r] at h
  exact Γ.gaugeCast_mem_grading (add_assoc a b c) h

/-- The intertwining hypothesis transports: the aligned identity against
`(gaugeRouteR', gaugeRouteL)` becomes the native one against
`(gaugeRouteR, gaugeRouteLNative)`.  The row reindex is
`Equiv.sum_comp (gaugeSizeCastEquiv hsz)` and the coefficient cast is
multiplicative, so the two identities are equivalent entry by entry. -/
theorem alignT_intertwine (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    (T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier) {e : ZMod 2}
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y)) :
    ∀ ⦃j : ZMod 2⦄ ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      routeRMat K Γ a b c y * alignT K Γ a b c hsz T
        = ((sgn (j * e) : ℤˣ) : ℤ) •
            (alignT K Γ a b c hsz T * routeLNativeMat K Γ a b c y) := by
  intro j y hy
  have hint0 : ((Γ.gaugeRouteR' a b c).toAlgEquiv y :
        Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
          (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
          (Γ.D (a + b + c)).carrier)
        * (T : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
            (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
            (Γ.D (a + b + c)).carrier)
      = ((sgn (j * e) : ℤˣ) : ℤ) •
          ((T : Matrix (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
              (Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2)
              (Γ.D (a + b + c)).carrier)
            * (Γ.gaugeRouteL a b c).toAlgEquiv y) := hT_int hy
  have hentry : ∀ i s : Fin (Γ.gaugeSizeL a b c).1 ⊕ Fin (Γ.gaugeSizeL a b c).2,
      (∑ i', (Γ.gaugeRouteR' a b c).toAlgEquiv y i i' * T i' s)
        = ((sgn (j * e) : ℤˣ) : ℤ) •
            ∑ s', T i s' * (Γ.gaugeRouteL a b c).toAlgEquiv y s' s := by
    intro i s
    exact congrFun (congrFun hint0 i) s
  have hR : ∀ r r' : Fin (Γ.gaugeSizeR a b c).1 ⊕ Fin (Γ.gaugeSizeR a b c).2,
      routeRMat K Γ a b c y r r'
        = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
            ((Γ.gaugeRouteR' a b c).toAlgEquiv y (gaugeSizeCastEquiv K Γ a b c hsz r)
              (gaugeSizeCastEquiv K Γ a b c hsz r')) := by
    intro r r'
    rw [routeR'_entry K Γ a b c hsz, Equiv.symm_apply_apply, Equiv.symm_apply_apply,
      gaugeCast_assoc_symm_cancel]
  refine Matrix.ext fun r s => ?_
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.mul_apply]
  calc (∑ r', routeRMat K Γ a b c y r r' * alignT K Γ a b c hsz T r' s)
      = ∑ r', (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          ((Γ.gaugeRouteR' a b c).toAlgEquiv y (gaugeSizeCastEquiv K Γ a b c hsz r)
              (gaugeSizeCastEquiv K Γ a b c hsz r')
            * T (gaugeSizeCastEquiv K Γ a b c hsz r') s) := by
        refine Finset.sum_congr rfl fun r' _ => ?_
        rw [hR r r', alignT_apply, ← map_mul]
    _ = ∑ i, (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          ((Γ.gaugeRouteR' a b c).toAlgEquiv y (gaugeSizeCastEquiv K Γ a b c hsz r) i
            * T i s) :=
        Equiv.sum_comp (gaugeSizeCastEquiv K Γ a b c hsz)
          (fun i => (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
            ((Γ.gaugeRouteR' a b c).toAlgEquiv y (gaugeSizeCastEquiv K Γ a b c hsz r) i
              * T i s))
    _ = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (∑ i, (Γ.gaugeRouteR' a b c).toAlgEquiv y (gaugeSizeCastEquiv K Γ a b c hsz r) i
            * T i s) := (map_sum _ _ _).symm
    _ = (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (((sgn (j * e) : ℤˣ) : ℤ) • ∑ s', T (gaugeSizeCastEquiv K Γ a b c hsz r) s'
            * (Γ.gaugeRouteL a b c).toAlgEquiv y s' s) := by
        rw [hentry]
    _ = ((sgn (j * e) : ℤˣ) : ℤ) • (Γ.gaugeCast (add_assoc a b c)).toAlgEquiv
          (∑ s', T (gaugeSizeCastEquiv K Γ a b c hsz r) s'
            * (Γ.gaugeRouteL a b c).toAlgEquiv y s' s) := map_zsmul _ _ _
    _ = ((sgn (j * e) : ℤˣ) : ℤ) • ∑ s', alignT K Γ a b c hsz T r s'
          * routeLNativeMat K Γ a b c y s' s := by
        refine congrArg (fun w => ((sgn (j * e) : ℤˣ) : ℤ) • w) ?_
        rw [map_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [map_mul, ← gaugeRouteLNative_entry, alignT_apply]

/-- **`TDictGauge.gtOfT_mem_interSpace`, re-derived through the native
device** — the concrete demonstration that one uniform device suffices: at a
triple where `hsz` holds, the aligned certificate is transported by `alignT`
and the native theorem is applied. -/
theorem gtOfT_mem_interSpace_via_native
    (hsz : Γ.gaugeSizeR a b c = Γ.gaugeSizeL a b c)
    {T : ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).carrier} {e : ZMod 2}
    (hT : T ∈ ((Γ.D (a + b + c)).matrixSuper (Γ.gaugeSizeL a b c).1
      (Γ.gaugeSizeL a b c).2).grading e)
    (hT_int : ∀ ⦃j : ZMod 2⦄
        ⦃y : (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).carrier⦄,
      y ∈ (((Γ.D a).gtensor (Γ.D b)).gtensor (Γ.D c)).grading j →
      (Γ.gaugeRouteR' a b c).toAlgEquiv y * T
        = ((sgn (j * e) : ℤˣ) : ℤ) • (T * (Γ.gaugeRouteL a b c).toAlgEquiv y)) :
    gtOfT K Γ a b c hsz T ∈ gInterSpace K Γ a b c e := by
  rw [gtOfT_eq_gtOfTNative K Γ a b c hsz T]
  exact gtOfTNative_mem_interSpace K Γ a b c
    (alignT_mem_nativeGrading K Γ a b c hsz hT)
    (alignT_intertwine K Γ a b c hsz T hT_int)

end Native

end GaugeChi

end Superfusion
