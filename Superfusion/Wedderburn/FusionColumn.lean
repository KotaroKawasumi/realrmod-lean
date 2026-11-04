/-
Superfusion / Wedderburn / FusionColumn

Milestone M11-1: **the general fusion column bimodule** — the gauge→bimodule
bridge.  For a matrix-form fusion isomorphism `φ : P ≅ M_{p|q}(B)` (a
`SuperAlgEquiv` between bundled superalgebras), the column space of the
matrix side, pulled back along `φ`, is a super `(P, B)`-bimodule
(`FusionColumn φ`): the right `B`-action and column grading are reused
verbatim from `Bimod.ColumnBimod`, and the left `P`-action is the matrix
action transported along `φ` (`Module.compHom`), following exactly the
type-synonym + `inferInstanceAs` discipline of `Bimod.TowerColumn`
(the concrete `ℤ/8` case, now the *template* this file generalizes).  When
`P = P₁.gtensor P₂` (the shape `bwFuse` produces), the two slot actions of
`P₁` and `P₂` (through `includeLeft`/`includeRight`) supercommute — reusing
`Bimod.GtensorSlots.superCommSMul_of_algHom` verbatim, since that lemma is
already stated for an arbitrary algebra map out of a graded tensor product,
with no tower-specific hypotheses.  Over a super division `B`
(`Bimod.IsSuperDivision B.grading`), every left-`P`-and-right-`B`-stable
homogeneous submodule of `FusionColumn φ` is `⊥` or `⊤`
(`FusionColumn.irreducible`): since `φ` is bijective, `P`-stability of a
submodule is literally matrix-stability transported along `φ`, so
`Bimod.ColumnSimple.columnBimodule_irreducible` applies after converting the
single hypothesis `hL` from `P`-elements to matrix elements via `φ.symm`.

Instantiating at the tautological BW gauge (`Superfusion.Wedderburn.BWGauge`)
gives `bwColumn a b := FusionColumn (bwFuse a b)`, the graded
`(bwRep a ᵍ⊗ bwRep b, bwRep (a+b))`-bimodule realizing the fusion datum
`F_{a,b}` of the skeletal data `(BW(K), D_a, F_{a,b})` in bimodule form — the
object the future abstract bimodule-isomorphism definition of `(p, χ)`
(relative-tensor composites, Hom super-lines) will consume; the concrete
`ℤ/8` analogue of this whole file is `Bimod.TowerColumn`.
-/
import Superfusion.Wedderburn.BWGauge
import Superfusion.Bimod.ColumnSimple
import Superfusion.Bimod.GtensorSlots

namespace Superfusion

namespace Bimod

open scoped TensorProduct

/-! ### The general fusion column -/

section General

variable {K : Type*} [CommRing K]
variable {P B : SuperAlgebra K} {p q : ℕ}

/-- **The general fusion column** (M11-1, deliverable 1): for a matrix-form
fusion isomorphism `φ : P ≅ M_{p|q}(B)`, the column space of the matrix side
`M_{p|q}(B)`, carrying the right `B`-action of `Bimod.ColumnBimod` and the
left `P`-action pulled back along `φ`. -/
def FusionColumn (_φ : SuperAlgEquiv P (B.matrixSuper p q)) : Type _ :=
  (Fin p ⊕ Fin q) → B.carrier

namespace FusionColumn

variable (φ : SuperAlgEquiv P (B.matrixSuper p q))

noncomputable instance : AddCommGroup (FusionColumn φ) :=
  inferInstanceAs (AddCommGroup ((Fin p ⊕ Fin q) → B.carrier))

noncomputable instance : Module K (FusionColumn φ) :=
  inferInstanceAs (Module K ((Fin p ⊕ Fin q) → B.carrier))

/-- The matrix action (`mulVec`), in its raw spelling. -/
noncomputable instance :
    Module (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) (FusionColumn φ) :=
  inferInstanceAs (Module (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier)
    ((Fin p ⊕ Fin q) → B.carrier))

/-- The right action of the coefficients (reused from `ColumnBimod`). -/
noncomputable instance : Module B.carrierᵐᵒᵖ (FusionColumn φ) :=
  inferInstanceAs (Module B.carrierᵐᵒᵖ ((Fin p ⊕ Fin q) → B.carrier))

instance : IsScalarTower K B.carrierᵐᵒᵖ (FusionColumn φ) :=
  inferInstanceAs (IsScalarTower K B.carrierᵐᵒᵖ ((Fin p ⊕ Fin q) → B.carrier))

/-- The column grading (reused from `ColumnBimod`). -/
noncomputable abbrev grading : ZMod 2 → Submodule K (FusionColumn φ) :=
  columnGrading (sumParity p q) B.grading

noncomputable instance : DirectSum.Decomposition (grading φ) :=
  inferInstanceAs
    (DirectSum.Decomposition (columnGrading (sumParity p q) B.grading))

instance : GradedRightSMul B.grading (grading φ) :=
  inferInstanceAs
    (GradedRightSMul B.grading (columnGrading (sumParity p q) B.grading))

/-- Bridge: the matrix action in the bundled `(B.matrixSuper p q).carrier`
spelling (both spellings are the same instance; registered separately for
instance search, since `Module.compHom`'s codomain — the target of
`φ.toAlgEquiv.toAlgHom.toRingHom` — is syntactically the bundled spelling,
which instance search does not unfold on its own). -/
noncomputable instance : Module (B.matrixSuper p q).carrier (FusionColumn φ) :=
  inferInstanceAs (Module (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier)
    ((Fin p ⊕ Fin q) → B.carrier))

noncomputable instance : SMulCommClass (B.matrixSuper p q).carrier B.carrierᵐᵒᵖ
    (FusionColumn φ) :=
  inferInstanceAs (SMulCommClass
    (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) B.carrierᵐᵒᵖ
    ((Fin p ⊕ Fin q) → B.carrier))

noncomputable instance : IsScalarTower K (B.matrixSuper p q).carrier
    (FusionColumn φ) :=
  inferInstanceAs (IsScalarTower K
    (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier)
    ((Fin p ⊕ Fin q) → B.carrier))

/-! ### The pulled-back left `P`-action -/

/-- The left `P`-action, pulled back along `φ`. -/
noncomputable instance : Module P.carrier (FusionColumn φ) :=
  Module.compHom _ φ.toAlgEquiv.toAlgHom.toRingHom

theorem smul_def (x : P.carrier) (v : FusionColumn φ) :
    x • v = (φ.toAlgEquiv x) • v := rfl

/-- Bridge: matrix membership pulled back along `φ` (`SuperAlgEquiv.map_grading`
composed with `Submodule.mem_map_of_mem`; the same route as
`TowerColumn.stdFuse_mem_matrixGrading`). -/
theorem mem_matrixGrading_of_mem {i : ZMod 2} {x : P.carrier}
    (hx : x ∈ P.grading i) :
    φ.toAlgEquiv x ∈ matrixGradingA (sumParity p q) B.grading i := by
  have h := Submodule.mem_map_of_mem (f := φ.toAlgEquiv.toLinearMap) hx
  rwa [φ.map_grading i] at h

/-- The left `P`-action is graded. -/
instance : SetLike.GradedSMul P.grading (grading φ) where
  smul_mem {i j} x v hx hv := by
    rw [vadd_eq_add]
    exact columnGrading_smul_mem (sumParity p q) B.grading
      (mem_matrixGrading_of_mem φ hx) hv

instance : IsScalarTower K P.carrier (FusionColumn φ) where
  smul_assoc k x v := by
    show (φ.toAlgEquiv (k • x)) • v = k • (φ.toAlgEquiv x • v)
    rw [map_smul]
    exact smul_assoc k (φ.toAlgEquiv x) v

/-- Bridge: commutation and tower for the raw matrix spelling. -/
noncomputable instance : SMulCommClass
    (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) B.carrierᵐᵒᵖ
    (FusionColumn φ) :=
  inferInstanceAs (SMulCommClass
    (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) B.carrierᵐᵒᵖ
    ((Fin p ⊕ Fin q) → B.carrier))

noncomputable instance : IsScalarTower K
    (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) (FusionColumn φ) :=
  inferInstanceAs (IsScalarTower K
    (Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier)
    ((Fin p ⊕ Fin q) → B.carrier))

/-- **The pulled-back left `P`-action strictly commutes with the right
coefficient action**: `FusionColumn φ` is a super `(P, B)`-bimodule package
in the sense of `Bimod.Basic` (M8a-1). -/
instance : SMulCommClass P.carrier B.carrierᵐᵒᵖ (FusionColumn φ) where
  smul_comm x d v := smul_comm
    (φ.toAlgEquiv x :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) d
    (v : (Fin p ⊕ Fin q) → B.carrier)

/-! ### Irreducibility -/

/-- **The fusion column is irreducible over a super division algebra `B`**
(M11-1, deliverable 3): transport of `columnBimodule_irreducible` along the
bijective pullback `φ` — `P`-stability of a submodule is literally
matrix-stability once every matrix is written as `φ x` for `x = φ.symm X`. -/
theorem irreducible (hdiv : IsSuperDivision B.grading)
    (s : Submodule K (FusionColumn φ))
    (hL : ∀ (x : P.carrier), ∀ v ∈ s, x • v ∈ s)
    (hR : ∀ (d : B.carrier), ∀ v ∈ s, MulOpposite.op d • v ∈ s)
    (hHom : s.IsHomogeneous (grading φ)) :
    s = ⊥ ∨ s = ⊤ := by
  refine columnBimodule_irreducible (sumParity p q) B.grading hdiv s ?_ hR hHom
  intro X v hv
  have h := hL (φ.toAlgEquiv.symm X) v hv
  rwa [smul_def, φ.toAlgEquiv.apply_symm_apply] at h

end FusionColumn

end General

/-! ### Slot actions for tensor sources -/

section Slots

variable {K : Type*} [CommRing K]
variable {P₁ P₂ B : SuperAlgebra K} {p q : ℕ}

namespace FusionColumn

variable (φ : SuperAlgEquiv (P₁.gtensor P₂) (B.matrixSuper p q))

/-- Bridge: the full `(P₁ ᵍ⊗ P₂)`-action (the general `P`-action of the
`General` section, specialized at `P := P₁.gtensor P₂`) in the raw `ᵍ⊗`
spelling — needed because `includeLeft`/`includeRight`'s stated codomain is
the raw `𝒜 ᵍ⊗[K] 𝒞` type, not the bundled `(P₁.gtensor P₂).carrier` spelling
that `Module.compHom` registers instances under (mirrors `TowerColumn`'s
"bridge: the action in the raw ᵍ⊗ spelling" instance). -/
noncomputable instance : Module (P₁.grading ᵍ⊗[K] P₂.grading) (FusionColumn φ) :=
  inferInstanceAs (Module (P₁.gtensor P₂).carrier (FusionColumn φ))

noncomputable instance : IsScalarTower K (P₁.grading ᵍ⊗[K] P₂.grading)
    (FusionColumn φ) :=
  inferInstanceAs (IsScalarTower K (P₁.gtensor P₂).carrier (FusionColumn φ))

/-- The `P₁`-slot action (through `x ↦ x ᵍ⊗ 1` and `φ`). -/
noncomputable instance instModuleSlotLeft : Module P₁.carrier (FusionColumn φ) :=
  Module.compHom _
    (φ.toAlgEquiv.toAlgHom.comp
      (GradedTensorProduct.includeLeft P₁.grading P₂.grading)).toRingHom

theorem slotLeft_smul_def (x : P₁.carrier) (v : FusionColumn φ) :
    x • v = φ.toAlgEquiv
      (GradedTensorProduct.includeLeft P₁.grading P₂.grading x) • v := rfl

/-- The `P₂`-slot action (through `y ↦ 1 ᵍ⊗ y` and `φ`). -/
noncomputable instance instModuleSlotRight : Module P₂.carrier (FusionColumn φ) :=
  Module.compHom _
    (φ.toAlgEquiv.toAlgHom.comp
      (GradedTensorProduct.includeRight P₁.grading P₂.grading)).toRingHom

theorem slotRight_smul_def (y : P₂.carrier) (v : FusionColumn φ) :
    y • v = φ.toAlgEquiv
      (GradedTensorProduct.includeRight P₁.grading P₂.grading y) • v := rfl

/-- **The two slot actions supercommute** (M11-1, deliverable 2): pushed
through `φ.toAlgEquiv.toAlgHom` from `Bimod.GtensorSlots.superCommSMul_of_algHom`,
which is *already* fully general (any algebra map out of a graded tensor
product, any module) — no tower-specific generalization was needed, exactly
mirroring `TowerColumn.superCommSMul`. -/
theorem superCommSMul : SuperCommSMul P₁.grading P₂.grading (FusionColumn φ) :=
  fun _ _ _ _ hx hc n =>
    superCommSMul_of_algHom P₁.grading P₂.grading φ.toAlgEquiv.toAlgHom hx hc n

/-- The `P₁`-slot action is graded. -/
instance : SetLike.GradedSMul P₁.grading (grading φ) where
  smul_mem {i j} x v hx hv := by
    rw [vadd_eq_add]
    exact columnGrading_smul_mem (sumParity p q) B.grading
      (mem_matrixGrading_of_mem φ (includeLeft_mem_tensorGrading _ _ hx)) hv

/-- The `P₂`-slot action is graded. -/
instance : SetLike.GradedSMul P₂.grading (grading φ) where
  smul_mem {i j} y v hy hv := by
    rw [vadd_eq_add]
    exact columnGrading_smul_mem (sumParity p q) B.grading
      (mem_matrixGrading_of_mem φ (includeRight_mem_tensorGrading _ _ hy)) hv

instance : SMulCommClass P₁.carrier B.carrierᵐᵒᵖ (FusionColumn φ) where
  smul_comm x d v := smul_comm
    (φ.toAlgEquiv (GradedTensorProduct.includeLeft P₁.grading P₂.grading x) :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) d
    (v : (Fin p ⊕ Fin q) → B.carrier)

instance : SMulCommClass P₂.carrier B.carrierᵐᵒᵖ (FusionColumn φ) where
  smul_comm y d v := smul_comm
    (φ.toAlgEquiv (GradedTensorProduct.includeRight P₁.grading P₂.grading y) :
      Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) B.carrier) d
    (v : (Fin p ⊕ Fin q) → B.carrier)

instance : IsScalarTower K P₁.carrier (FusionColumn φ) where
  smul_assoc k x v := by
    show (GradedTensorProduct.includeLeft P₁.grading P₂.grading (k • x)) • v
      = k • ((GradedTensorProduct.includeLeft P₁.grading P₂.grading x) • v)
    rw [map_smul]
    exact smul_assoc k
      (GradedTensorProduct.includeLeft P₁.grading P₂.grading x) v

instance : IsScalarTower K P₂.carrier (FusionColumn φ) where
  smul_assoc k y v := by
    show (GradedTensorProduct.includeRight P₁.grading P₂.grading (k • y)) • v
      = k • ((GradedTensorProduct.includeRight P₁.grading P₂.grading y) • v)
    rw [map_smul]
    exact smul_assoc k
      (GradedTensorProduct.includeRight P₁.grading P₂.grading y) v

end FusionColumn

end Slots

end Bimod

/-! ### The BW instantiation -/

section BW

variable {K : Type*} [Field K] [Invertible (2 : K)]

namespace Bimod

/-- **`bwColumn a b`, the fusion datum `F_{a,b}` in bimodule form** (M11-1,
deliverable 4): the graded `(bwRep a ᵍ⊗ bwRep b, bwRep (a+b))`-bimodule
realizing the fusion isomorphism `bwFuse a b` of the tautological BW gauge as
a `FusionColumn`.  This is the paper's fusion datum of the skeletal data
`(BW(K), D_a, F_{a,b})`; the abstract bimodule-isomorphism definition of
`(p, χ)` (routing relative-tensor composites and Hom super-lines) will
consume exactly these objects.  The concrete `ℤ/8` analogue is
`Bimod.TowerColumn`. -/
noncomputable abbrev bwColumn (a b : Additive (BW K)) : Type _ :=
  FusionColumn (bwFuse a b)

/-- **`bwColumn a b` is irreducible**: every left-`(bwRep a ᵍ⊗ bwRep
b)`-and-right-`bwRep (a+b)`-stable homogeneous submodule is `⊥` or `⊤`
(from `FusionColumn.irreducible` and `bwRep_isSuperDivision`). -/
theorem bwColumn_irreducible (a b : Additive (BW K))
    (s : Submodule K (bwColumn a b))
    (hL : ∀ (x : ((bwRep a).gtensor (bwRep b)).carrier), ∀ v ∈ s, x • v ∈ s)
    (hR : ∀ (d : (bwRep (a + b)).carrier), ∀ v ∈ s, MulOpposite.op d • v ∈ s)
    (hHom : s.IsHomogeneous (FusionColumn.grading (bwFuse a b))) :
    s = ⊥ ∨ s = ⊤ :=
  FusionColumn.irreducible (bwFuse a b) (bwRep_isSuperDivision (a + b)) s hL hR hHom

end Bimod

end BW

end Superfusion
