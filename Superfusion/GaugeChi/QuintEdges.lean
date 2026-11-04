/-
Superfusion / GaugeChi / QuintEdges

Milestone M13-2 of the abstract `(p, χ)` arc: **the 21 quintuple edge
maps** (`docs/m13-design.md`'s combinatorial ledger), built on the 14
vertex types of `GaugeChi.Quint`.

**Naming**: `E1M .. E21M` (the `M`-suffix avoids clashing with
`Bimod`'s own `E`-names for the 4-letter pentagon).

**The discipline** (referee correction 3): each edge is defined by
FIXED data — the canonical `gTCanon`/`gt2Canon` intertwiners at the
move's own triple, never a free parameter — via ONE face-aligned
presentation (recorded in each edge's docstring); the OTHER owning
face's derivation of the same edge becomes a recognition lemma,
deferred to the face-construction rounds (M13-3..5).

**The toolkit landed this round** (deferred from `Quint.lean`):

1. `gCanonRight`/`gCanonHphi4`/`gCanonHphi5`: public re-statements of
   `ChiCanon.lean`'s `private` one-line lemmas of the same content
   (`canon_right`/`canon_hφ₄`/`canon_hφ₅`) — needed verbatim here but
   inaccessible across the file boundary; reproved from the same public
   `gTCanon_mem_gInterSpace` source, zero new content.
2. **`gHomExtAssoc`**: a "curried" extensionality principle for a
   doubly-iterated balanced tensor `(M ⊗[A] N) ⊗[B] P` (two `K`-linear
   maps out of it agreeing on the fully-decomposed generators
   `mk (mk m n) p` already agree), proved abstractly (no `def`-wrapped
   vertex type involved). **Landed but NOT reusable as-is** for the
   vertex-level facts below: instantiating it against a `def`-wrapped
   codomain (`GBL`/`GQ1`/`GQ3`/…) triggers an `instances`-transparency
   mismatch between that type's OWN registered `AddCommGroup`/`Module`
   instances (routed through `inferInstanceAs`) and a freshly-elaborated
   raw `RelTensor` spelling of the "same" type — a SHARPER, term-level
   form of `Quint.lean`'s documented induction trap (it now also hits
   plain `.comp`/`rw`/`induction … using RelTensor.induction_on` on a
   `def`-wrapped type, not only the motive-synthesis case `Quint.lean`
   recorded). The WORKING discipline actually used below: (i) state
   every `Total`-equivariance fact POINTWISE with the registered `Total`
   `•` on both sides (never raw `rightActionEnd` compared through
   `.comp` against a `def`-wrapped codomain); (ii) `induction … using
   RelTensor.induction_on` IS safe directly on a `def`-wrapped variable
   PROVIDED its declared type in the surrounding statement already
   matches the induction's own raw spelling (no earlier `GBL Γ x y z`-
   named commitment elsewhere in the same term); (iii) the "mk" case's
   `RelTensor.mk`-generator must be re-shown into the OTHER face's named
   `X.mk`-spelling via `show` before invoking that face's own `_mk`
   lemma; (iv) the "add"/"zero" cases must be closed by TERM-MODE
   composition (`congrArg`, `.trans`, `map_add`/`map_zero`/`LinearMap.
   map_add₂` applied as terms) — `rw`/`simp` on the summed variable
   itself resurfaces the same transparency wall. This discipline is
   recorded here in full because it is the load-bearing discovery of
   the round and will recur for every remaining assoc-conjugated edge.
3. **The `Total`-action unfold lemmas** (`GQ1Total_op_smul_def` ..
   `GQ5Total_op_smul_def`, `GQ3InnerTotal_op_smul_def`): `rfl`-bridges
   from `Quint.lean`'s `Module.compHom`-packaged `Total` instances to
   the raw `rightActionEnd` applications, mirroring `Pentagon.lean`'s
   own `_op_smul_def` style.
4. **`assoc`'s `Total`-naturality**, per the discipline above:
   `gq3Assoc_rightTotal` (+ its `z`-level generalization
   `gq3Assoc_rightTotal_general`, since `gq3Assoc`'s OWN domain is a
   RAW type distinct from `GQ3`) and `gq1Assoc_rightTotal` (`gq1Assoc`'s
   domain literally IS `GQ1`, needing one MORE nested nesting level
   instead, since its first factor `GBL Γ p q r` is itself `RelTensor`-
   shaped). `gq2Assoc_rightTotal` (needed for the `GE2`-style edges 2/7)
   is NOT landed — deferred, see the closing note.
5. **`GE1_rightTotal`, `GE3_rightTotal`, `GE4_rightTotal`**: generic
   (any quadruple `p q r s : G`) `Total`-`D_{p+q+r+s}`-equivariance of
   the FIXED (`gTCanon`-instantiated) pentagon edges `GE1`/`GE3`/`GE4`
   (`PentagonEdges.lean`), reused VERBATIM at both quintuple
   instantiations `(p,q,r,s) := (a,b,c,d)` and `(p,q,r,s) := (b,c,d,e)`
   — the mirror-image structure the design's ledger predicts (`V10..
   V14` share `V1..V5`'s exact `RelTensor.map (GE_k) id` shape, only the
   outer `FusionColumn` slot flips from `F_{sum,e}` to `F_{a,sum}`, both
   handled generically by `rightActionEnd`). `GE2_rightTotal` (needing
   `gq2Assoc_rightTotal` plus the already-public `gt2Canon_rightSlot`)
   is NOT landed.

**Edges landed this round** (8 of 21; grouped by genre):

* **S-adjacent, no `GQ`-`Total` layer at all** (`E12M`, `E20M`): a bare
  whiskered `gTCanon` at the move's own triple, `RelTensor.map _ id`
  directly on the vertex's own top-level `GBL`/`GBR` factor — the
  simplest genre.
* **`GE1`-style** (`E1M`, `E6M`): `RelTensor.map (GE1 gTCanon) id`.
* **`GE3`-style** (`E3M`, `E8M`): `RelTensor.map (GE3 gTCanon) id`,
  needs `gq3Assoc`'s `Total`-naturality.
* **`GE4`-style** (`E4M`, `E9M`): `RelTensor.map (GE4 gTCanon) id`,
  needs `gq1Assoc`'s `Total`-naturality.

Each landed edge carries its own bijectivity theorem
(`E_kM_bijective`), assembled from `PentagonB.RelTensor.map_bijective_left`
/`PentagonB.smap_bijective` plus the already-bijective associators —
mirroring `gTopRoute_bijective`'s own assembly one level down.

**Remaining (13 of 21), precisely scoped:**

* `E2M`, `E7M` (`GE2`-style): need `gq2Assoc_rightTotal` — mechanically
  the SAME nested-induction discipline as `gq1Assoc_rightTotal` (one
  extra decomposition level, since `GE2`'s inner move lands in
  `GQ2rInner`/`GQ3Inner`, requiring `gt2Canon_rightSlot`, ALREADY
  public, for the outer-recast half); the closest remaining edges to
  landing.
* `E5M`, `E10M` (`GE5`+`gq4Close`-composite): need `gq5Swap`'s (a
  MIDDLE SWAP, not a plain `assoc`) and `gq4Close`'s (an `assoc` PLUS a
  `fusionColumnCast` recast layer) own `Total`-naturality — two further
  new toolkit facts beyond this round's.
* `E13M`, `E15M`: need a `FourLetterRecast`-style cast one level up
  from `gq2rCast` (genuinely new content, not a reuse of any landed
  fact) plus TWO assoc layers each — the design's own "cluster-tier"
  difficulty, despite being listed among the "simpler" fallback genre;
  the referee's fallback description undercounts these two.
* The cluster edges `E11M`, `E14M`, `E16M`, `E17M`, `E18M`, `E19M`,
  `E21M`: not attempted this round (multiple assoc/recast layers each,
  per the design's own risk note).
* Bijectivity of all of the above (once landed).
* `Nontrivial (V1 ..)`: scoped, not landed, per the referee's own
  recommendation — deferred to a dedicated round (`gq1Collapse`
  transported `D`-equivariantly through `V1`'s first slot), only
  needed at M13-6.
-/
import Superfusion.GaugeChi.Quint
import Superfusion.GaugeChi.ChiCanon

namespace Superfusion

namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Γ : DivisionFusionGauge K G)

attribute [local instance 500] leftModule rightModule

/-! ### Toolkit piece 1: the public re-statements of `ChiCanon.lean`'s
`private` one-liners -/

/-- **The right-recast equivariance of `gTCanon Γ x y z`** (public
re-statement of `ChiCanon.lean`'s `private canon_right`, needed
verbatim across the file boundary — reproved from the same public
`gTCanon_mem_gInterSpace` source). -/
theorem gCanonRight (x y z : G) :
    ∀ (τ : (Γ.D (x + y + z)).carrier) (m : GBL Γ x y z),
      gTCanon K Γ x y z (MulOpposite.op τ • m) = MulOpposite.op τ • gTCanon K Γ x y z m :=
  (mem_rightSemilinear
      (ψ := (Γ.gaugeCast (add_assoc x y z)).toAlgEquiv.toAlgHom.toRingHom)).mp
    ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).2.2.2.2

/-- **The signed `(x+y)`-slot equivariance of `gTCanon Γ (x+y) z w`**
(public re-statement of `ChiCanon.lean`'s `private canon_hφ₄`). -/
theorem gCanonHphi4 (x y z w : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (x + y)).carrier⦄,
      τ ∈ (Γ.D (x + y)).grading i → ∀ n : GBL Γ (x + y) z w,
        gTCanon K Γ (x + y) z w (τ • n)
          = ((sgn (gParity K Γ (x + y) z w * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ (x + y) z w n) :=
  (mem_superEquivariant (Γ.D (x + y)).grading).mp
    ((mem_gInterSpace_iff K Γ (x + y) z w).mp (gTCanon_mem_gInterSpace K Γ (x + y) z w)).2.1

/-- **The signed `(z+w)`-slot equivariance of `gTCanon Γ x y (z+w)`**
(public re-statement of `ChiCanon.lean`'s `private canon_hφ₅`). -/
theorem gCanonHphi5 (x y z w : G) :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (z + w)).carrier⦄,
      τ ∈ (Γ.D (z + w)).grading i → ∀ n : GBL Γ x y (z + w),
        gTCanon K Γ x y (z + w) (τ • n)
          = ((sgn (gParity K Γ x y (z + w) * i) : ℤˣ) : ℤ) • (τ • gTCanon K Γ x y (z + w) n) :=
  (mem_superEquivariant (Γ.D (z + w)).grading).mp
    ((mem_gInterSpace_iff K Γ x y (z + w)).mp (gTCanon_mem_gInterSpace K Γ x y (z + w))).2.2.2.1

/-! ### Toolkit piece 2: the curried extensionality principle for
`(M ⊗[A] N) ⊗[B] P` -/

section HomExtAssoc

variable {A : Type*} [Ring A] [Algebra K A]
variable {B : Type*} [Ring B] [Algebra K B]
variable {M : Type*} [AddCommGroup M] [Module K M] [Module Aᵐᵒᵖ M]
variable {N : Type*} [AddCommGroup N] [Module K N] [Module A N]
  [Module Bᵐᵒᵖ N] [SMulCommClass A Bᵐᵒᵖ N] [IsScalarTower K A N] [IsScalarTower K Bᵐᵒᵖ N]
variable {P : Type*} [AddCommGroup P] [Module K P] [Module B P]
variable {Q : Type*} [AddCommGroup Q] [Module K Q]

omit [Invertible (2 : K)] [Algebra K A] [IsScalarTower K A N] in
/-- **The curried extensionality principle**: two `K`-linear maps out of
the doubly-iterated balanced tensor `(M ⊗[A] N) ⊗[B] P` agreeing on the
FULLY-decomposed generators `mk (mk m n) p` already agree — proved by
nesting `RelTensor.hom_ext` with an inner `RelTensor.induction_on` on
the *raw* `M ⊗[A;K] N` (never a `def`-wrapped vertex type), sidestepping
`Quint.lean`'s documented induction elaboration trap by construction. -/
theorem gHomExtAssoc
    {g h : ((M ⊗[A;K] N) ⊗[B;K] P) →ₗ[K] Q}
    (H : ∀ (m : M) (n : N) (p : P),
      g (RelTensor.mk K B (M ⊗[A;K] N) P (RelTensor.mk K A M N m n) p)
        = h (RelTensor.mk K B (M ⊗[A;K] N) P (RelTensor.mk K A M N m n) p)) :
    g = h := by
  refine RelTensor.hom_ext fun z p => ?_
  induction z using RelTensor.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply]
  | mk m n => exact H m n p
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, hx, hy]

end HomExtAssoc

variable (a b c d e : G)

/-! ### Toolkit piece 3: the `Total`-action unfold lemmas -/

theorem GQ1Total_op_smul_def (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ1 K Γ p q r s) :
    MulOpposite.op τ • m
      = rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
          (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) m := rfl

theorem GQ2Total_op_smul_def (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ2 K Γ p q r s) :
    MulOpposite.op τ • m
      = rightActionEnd K (Γ.D (p + q + r)).carrier (GBR Γ p q r)
          (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) m := rfl

theorem GQ3Total_op_smul_def (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ3 K Γ p q r s) :
    MulOpposite.op τ • m
      = rightActionEnd K (Γ.D (q + r)).carrier (FusionColumn (Γ.fuse q r))
          (GQ3Inner K Γ p q r s) (MulOpposite.op τ) m := rfl

theorem GQ4Total_op_smul_def (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ4 K Γ p q r s) :
    MulOpposite.op τ • m
      = rightActionEnd K (Γ.D (q + r + s)).carrier (GBR Γ q r s)
          (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) m := rfl

theorem GQ5Total_op_smul_def (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ5 K Γ p q r s) :
    MulOpposite.op τ • m
      = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
          (GBR Γ (p + q) r s) (MulOpposite.op τ) m := rfl

theorem GQ3InnerTotal_op_smul_def (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (n : GQ3Inner K Γ p q r s) :
    MulOpposite.op τ • n
      = rightActionEnd K (Γ.D (q + r + s)).carrier (FusionColumn (Γ.fuse (q + r) s))
          (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) n := rfl

/-! ### Toolkit piece 4: `assoc`'s `Total`-naturality, per associator -/

/-- **`gq3Assoc`'s `Total`-naturality**: the associator at the
`a((bc)d)`-vertex intertwines the outer `D_{p+q+r+s}`-action (the
`GQ3Inner`/`GQ3` `Total`-actions of `Quint.lean`'s ledger, acting through
the LAST tensor factor on both sides) — sign-free (`RelTensor.assoc`
never signs). Stated POINTWISE with the registered `Total` `•`
notation throughout (never a raw `rightActionEnd` compared against a
`def`-wrapped codomain via `.comp`) — the discipline that sidesteps the
`instances`-transparency mismatch between a `def`-wrapped vertex type's
OWN registered instances and a freshly-elaborated raw `RelTensor`
spelling of the "same" type. -/
theorem gq3Assoc_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : FusionColumn (Γ.fuse q r) ⊗[(Γ.D (q + r)).carrier;K] FusionColumn (Γ.fuse (q + r) s))
    (w : FusionColumn (Γ.fuse p (q + r + s))) :
    gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
        (FusionColumn (Γ.fuse p (q + r + s))) m (MulOpposite.op τ • w))
      = MulOpposite.op τ • gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier
          (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s))) m w) := by
  induction m using RelTensor.induction_on with
  | zero =>
      show gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
          (FusionColumn (Γ.fuse p (q + r + s))) (0 : GBL Γ q r s) (MulOpposite.op τ • w))
        = MulOpposite.op τ • gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier
            (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s))) (0 : GBL Γ q r s) w)
      simp only [map_zero, LinearMap.zero_apply, smul_zero]
  | mk u v =>
      show gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
          (FusionColumn (Γ.fuse p (q + r + s))) (GBL.mk Γ q r s u v) (MulOpposite.op τ • w))
        = MulOpposite.op τ • gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier
            (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s))) (GBL.mk Γ q r s u v) w)
      rw [gq3Assoc_mk, gq3Assoc_mk, GQ3Total_op_smul_def, rightActionEnd_mk,
        GQ3InnerTotal_op_smul_def, rightActionEnd_mk]
  | add x y hx hy =>
      have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
        (FusionColumn (Γ.fuse p (q + r + s)))) x y (MulOpposite.op τ • w)
      have e2 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
        (FusionColumn (Γ.fuse p (q + r + s)))) x y w
      calc gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
            (FusionColumn (Γ.fuse p (q + r + s))) (x + y) (MulOpposite.op τ • w))
          = gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                (FusionColumn (Γ.fuse p (q + r + s))) x (MulOpposite.op τ • w)
              + RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                (FusionColumn (Γ.fuse p (q + r + s))) y (MulOpposite.op τ • w)) :=
              congrArg (gq3Assoc K Γ p q r s) e1
        _ = gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                (FusionColumn (Γ.fuse p (q + r + s))) x (MulOpposite.op τ • w))
            + gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                (FusionColumn (Γ.fuse p (q + r + s))) y (MulOpposite.op τ • w)) := map_add _ _ _
        _ = MulOpposite.op τ • gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier
                (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s))) x w)
            + MulOpposite.op τ • gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier
                (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s))) y w) := by rw [hx, hy]
        _ = MulOpposite.op τ •
              (gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                  (FusionColumn (Γ.fuse p (q + r + s))) x w)
                + gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                  (FusionColumn (Γ.fuse p (q + r + s))) y w)) := (smul_add _ _ _).symm
        _ = MulOpposite.op τ • gq3Assoc K Γ p q r s (RelTensor.mk K (Γ.D (q + r + s)).carrier
              (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s))) (x + y) w) :=
            congrArg (MulOpposite.op τ • ·)
              ((congrArg (gq3Assoc K Γ p q r s) e2).trans (map_add _ _ _)).symm

/-! ### Toolkit piece 5: `GE1`'s generic `Total`-equivariance -/

/-- **`GE1`'s `Total`-equivariance**, at the FIXED `gTCanon`-instantiated
generator, generic over any quadruple `p q r s : G` — reused VERBATIM at
`(a,b,c,d)` (edge 1) and `(b,c,d,e)` (edge 6). -/
theorem GE1_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ1 K Γ p q r s) :
    GE1 K Γ p q r s (gTCanon K Γ p q r).toLinearMap (gCanonRight K Γ p q r)
        (MulOpposite.op τ • m)
      = MulOpposite.op τ •
          GE1 K Γ p q r s (gTCanon K Γ p q r).toLinearMap (gCanonRight K Γ p q r) m := by
  rw [GQ1Total_op_smul_def, GQ2Total_op_smul_def]
  exact LinearMap.congr_fun
    (map_comp_rightActionEnd (A := (Γ.D (p + q + r)).carrier)
      (gTCanon K Γ p q r).toLinearMap
      (LinearMap.id (R := K) (M := FusionColumn (Γ.fuse (p + q + r) s)))
      (gCanonRight K Γ p q r) (fun _ _ => rfl) (e := MulOpposite.op τ) (fun _ => rfl)) m

/-! ### Toolkit piece 6: `GE3`'s generic `Total`-equivariance -/

/-- **`gq3Assoc`'s `Total`-naturality, at the level of its own domain**
(the `z`-generalization of `gq3Assoc_rightTotal`, extending the
generator-level fact to every `z` by linearity, via the SAME
`show`/term-mode discipline). -/
theorem gq3Assoc_rightTotal_general (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (z : RelTensor K (Γ.D (q + r + s)).carrier (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s)))) :
    gq3Assoc K Γ p q r s
        (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
          (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) z)
      = MulOpposite.op τ • gq3Assoc K Γ p q r s z := by
  induction z using RelTensor.induction_on with
  | zero =>
      calc gq3Assoc K Γ p q r s
            (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
              (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) 0)
          = gq3Assoc K Γ p q r s 0 := congrArg (gq3Assoc K Γ p q r s) (map_zero _)
        _ = 0 := map_zero _
        _ = MulOpposite.op τ • (0 : GQ3 K Γ p q r s) := (smul_zero _).symm
        _ = MulOpposite.op τ • gq3Assoc K Γ p q r s 0 :=
            congrArg (MulOpposite.op τ • ·) (map_zero _).symm
  | mk m w =>
      rw [rightActionEnd_mk]
      exact gq3Assoc_rightTotal K Γ p q r s τ m w
  | add x y hx hy =>
      have e := map_add (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
        (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ)) x y
      calc gq3Assoc K Γ p q r s
            (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
              (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) (x + y))
          = gq3Assoc K Γ p q r s
              (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                  (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) x
                + rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
                  (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) y) :=
            congrArg (gq3Assoc K Γ p q r s) e
        _ = gq3Assoc K Γ p q r s (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
              (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) x)
            + gq3Assoc K Γ p q r s (rightActionEnd K (Γ.D (q + r + s)).carrier (GBL Γ q r s)
              (FusionColumn (Γ.fuse p (q + r + s))) (MulOpposite.op τ) y) := map_add _ _ _
        _ = MulOpposite.op τ • gq3Assoc K Γ p q r s x + MulOpposite.op τ • gq3Assoc K Γ p q r s y := by
            rw [hx, hy]
        _ = MulOpposite.op τ • (gq3Assoc K Γ p q r s x + gq3Assoc K Γ p q r s y) := (smul_add _ _ _).symm
        _ = MulOpposite.op τ • gq3Assoc K Γ p q r s (x + y) := congrArg (MulOpposite.op τ • ·) (map_add _ _ _).symm

/-- **`GE3` factors `gq3Assoc`**: `GE3 ∘ gq3Assoc = map(t₃,id)` on the
associator's own domain — the definitional cancellation
`gq3Assoc.symm ∘ gq3Assoc = id`. -/
theorem GE3_comp_gq3Assoc (p q r s : G) (t₃ : GBL Γ q r s →ₗ[K] GBR Γ q r s)
    (ht₃ : ∀ (τ : (Γ.D (q + r + s)).carrier) (m : GBL Γ q r s),
      t₃ (MulOpposite.op τ • m) = MulOpposite.op τ • t₃ m)
    (z : RelTensor K (Γ.D (q + r + s)).carrier (GBL Γ q r s) (FusionColumn (Γ.fuse p (q + r + s)))) :
    GE3 K Γ p q r s t₃ ht₃ (gq3Assoc K Γ p q r s z)
      = RelTensor.map t₃ LinearMap.id ht₃ (fun _ _ => rfl) z := by
  show RelTensor.map t₃ LinearMap.id ht₃ (fun _ _ => rfl)
      ((gq3Assoc K Γ p q r s).symm (gq3Assoc K Γ p q r s z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- **`GE3`'s `Total`-equivariance**, at the FIXED `gTCanon`-instantiated
generator, generic over any quadruple `p q r s : G` — reused VERBATIM at
`(a,b,c,d)` (edge 3) and `(b,c,d,e)` (edge 8). -/
theorem GE3_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (n : GQ3 K Γ p q r s) :
    GE3 K Γ p q r s (gTCanon K Γ q r s).toLinearMap (gCanonRight K Γ q r s)
        (MulOpposite.op τ • n)
      = MulOpposite.op τ •
          GE3 K Γ p q r s (gTCanon K Γ q r s).toLinearMap (gCanonRight K Γ q r s) n := by
  have hn : n = gq3Assoc K Γ p q r s ((gq3Assoc K Γ p q r s).symm n) :=
    ((gq3Assoc K Γ p q r s).apply_symm_apply n).symm
  set z := (gq3Assoc K Γ p q r s).symm n
  rw [hn, ← gq3Assoc_rightTotal_general, GE3_comp_gq3Assoc, GE3_comp_gq3Assoc,
    GQ4Total_op_smul_def]
  exact LinearMap.congr_fun
    (map_comp_rightActionEnd (A := (Γ.D (q + r + s)).carrier)
      (gTCanon K Γ q r s).toLinearMap
      (LinearMap.id (R := K) (M := FusionColumn (Γ.fuse p (q + r + s))))
      (gCanonRight K Γ q r s) (fun _ _ => rfl) (e := MulOpposite.op τ) (fun _ => rfl)) z

/-! ### Toolkit piece 7: `gq1Assoc`'s and `GE4`'s generic `Total`-equivariance -/

/-- **`gq1Assoc`'s `Total`-naturality**: `gq1Assoc`'s domain literally
IS `GQ1` (no separate `z`-level domain unlike `gq3Assoc`), so this is
stated directly at `m : GQ1`; the target side lands in `GBL Γ (p+q) r s`
directly (its OWN natural `Total`, no recast). -/
theorem gq1Assoc_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ1 K Γ p q r s) :
    gq1Assoc K Γ p q r s (MulOpposite.op τ • m)
      = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
          (GBL Γ (p + q) r s) (MulOpposite.op τ) (gq1Assoc K Γ p q r s m) := by
  rw [GQ1Total_op_smul_def]
  induction m using RelTensor.induction_on with
  | zero =>
      calc gq1Assoc K Γ p q r s
            (rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
              (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) 0)
          = gq1Assoc K Γ p q r s 0 := congrArg (gq1Assoc K Γ p q r s) (map_zero _)
        _ = 0 := map_zero _
        _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
              (GBL Γ (p + q) r s) (MulOpposite.op τ) 0 := (map_zero _).symm
        _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
              (GBL Γ (p + q) r s) (MulOpposite.op τ) (gq1Assoc K Γ p q r s 0) :=
            congrArg _ (map_zero _).symm
  | mk u v =>
      rw [rightActionEnd_mk]
      induction u using RelTensor.induction_on with
      | zero =>
          show gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
              (FusionColumn (Γ.fuse (p + q + r) s)) (0 : GBL Γ p q r) (MulOpposite.op τ • v))
            = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
                (GBL Γ (p + q) r s) (MulOpposite.op τ)
                (gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                  (FusionColumn (Γ.fuse (p + q + r) s)) (0 : GBL Γ p q r) v))
          have e0 : RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                (FusionColumn (Γ.fuse (p + q + r) s)) (0 : GBL Γ p q r) (MulOpposite.op τ • v)
              = (0 : GQ1 K Γ p q r s) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (p + q + r)).carrier
              (GBL Γ p q r) (FusionColumn (Γ.fuse (p + q + r) s)))) (MulOpposite.op τ • v)).trans
              (LinearMap.zero_apply _)
          have e0' : RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                (FusionColumn (Γ.fuse (p + q + r) s)) (0 : GBL Γ p q r) v
              = (0 : GQ1 K Γ p q r s) :=
            (LinearMap.congr_fun (map_zero (RelTensor.mk K (Γ.D (p + q + r)).carrier
              (GBL Γ p q r) (FusionColumn (Γ.fuse (p + q + r) s)))) v).trans
              (LinearMap.zero_apply _)
          rw [e0, e0', map_zero, map_zero]
      | mk u' v' =>
          show gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
              (FusionColumn (Γ.fuse (p + q + r) s)) (GBL.mk Γ p q r u' v') (MulOpposite.op τ • v))
            = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
                (GBL Γ (p + q) r s) (MulOpposite.op τ)
                (gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                  (FusionColumn (Γ.fuse (p + q + r) s)) (GBL.mk Γ p q r u' v') v))
          rw [gq1Assoc_mk, gq1Assoc_mk, rightActionEnd_mk, GBL.right_smul_mk]
      | add x y hx hy =>
          have e1 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
            (FusionColumn (Γ.fuse (p + q + r) s))) x y (MulOpposite.op τ • v)
          have e2 := LinearMap.map_add₂ (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
            (FusionColumn (Γ.fuse (p + q + r) s))) x y v
          calc gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                (FusionColumn (Γ.fuse (p + q + r) s)) (x + y) (MulOpposite.op τ • v))
              = gq1Assoc K Γ p q r s
                  (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                      (FusionColumn (Γ.fuse (p + q + r) s)) x (MulOpposite.op τ • v)
                    + RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                      (FusionColumn (Γ.fuse (p + q + r) s)) y (MulOpposite.op τ • v)) :=
                congrArg (gq1Assoc K Γ p q r s) e1
            _ = gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                    (FusionColumn (Γ.fuse (p + q + r) s)) x (MulOpposite.op τ • v))
                + gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                    (FusionColumn (Γ.fuse (p + q + r) s)) y (MulOpposite.op τ • v)) := map_add _ _ _
            _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
                  (GBL Γ (p + q) r s) (MulOpposite.op τ)
                  (gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                    (FusionColumn (Γ.fuse (p + q + r) s)) x v))
                + rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
                  (GBL Γ (p + q) r s) (MulOpposite.op τ)
                  (gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                    (FusionColumn (Γ.fuse (p + q + r) s)) y v)) := by rw [hx, hy]
            _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
                  (GBL Γ (p + q) r s) (MulOpposite.op τ)
                  (gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                      (FusionColumn (Γ.fuse (p + q + r) s)) x v)
                    + gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                      (FusionColumn (Γ.fuse (p + q + r) s)) y v)) := (map_add _ _ _).symm
            _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
                  (GBL Γ (p + q) r s) (MulOpposite.op τ)
                  (gq1Assoc K Γ p q r s (RelTensor.mk K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                    (FusionColumn (Γ.fuse (p + q + r) s)) (x + y) v)) :=
                congrArg _ (congrArg (gq1Assoc K Γ p q r s) e2).symm
  | add x y hx hy =>
      have e := map_add (rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
        (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ)) x y
      calc gq1Assoc K Γ p q r s
            (rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
              (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) (x + y))
          = gq1Assoc K Γ p q r s
              (rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                  (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) x
                + rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
                  (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) y) :=
            congrArg (gq1Assoc K Γ p q r s) e
        _ = gq1Assoc K Γ p q r s (rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
              (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) x)
            + gq1Assoc K Γ p q r s (rightActionEnd K (Γ.D (p + q + r)).carrier (GBL Γ p q r)
              (FusionColumn (Γ.fuse (p + q + r) s)) (MulOpposite.op τ) y) := map_add _ _ _
        _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
              (GBL Γ (p + q) r s) (MulOpposite.op τ) (gq1Assoc K Γ p q r s x)
            + rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
              (GBL Γ (p + q) r s) (MulOpposite.op τ) (gq1Assoc K Γ p q r s y) := by rw [hx, hy]
        _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
              (GBL Γ (p + q) r s) (MulOpposite.op τ)
              (gq1Assoc K Γ p q r s x + gq1Assoc K Γ p q r s y) := (map_add _ _ _).symm
        _ = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q))
              (GBL Γ (p + q) r s) (MulOpposite.op τ) (gq1Assoc K Γ p q r s (x + y)) :=
            congrArg _ (map_add _ _ _).symm

/-- **`GE4`'s `Total`-equivariance**, at the FIXED `gTCanon`-instantiated
generator, generic over any quadruple `p q r s : G` — reused VERBATIM at
`(a,b,c,d)` (edge 4) and `(b,c,d,e)` (edge 9). -/
theorem GE4_rightTotal (p q r s : G) (τ : (Γ.D (p + q + r + s)).carrier)
    (m : GQ1 K Γ p q r s) :
    GE4 K Γ p q r s (gParity K Γ (p + q) r s) (gTCanon K Γ (p + q) r s).toLinearMap
        (gCanonHphi4 K Γ p q r s) (MulOpposite.op τ • m)
      = MulOpposite.op τ • GE4 K Γ p q r s (gParity K Γ (p + q) r s)
          (gTCanon K Γ (p + q) r s).toLinearMap (gCanonHphi4 K Γ p q r s) m := by
  rw [GQ5Total_op_smul_def]
  show (smap (Γ.D (p + q)).grading (FusionColumn.grading (Γ.fuse p q))
        (gTCanon K Γ (p + q) r s).toLinearMap (gParity K Γ (p + q) r s) (gCanonHphi4 K Γ p q r s))
      (gq1Assoc K Γ p q r s (MulOpposite.op τ • m))
    = rightActionEnd K (Γ.D (p + q)).carrier (FusionColumn (Γ.fuse p q)) (GBR Γ (p + q) r s)
        (MulOpposite.op τ)
        ((smap (Γ.D (p + q)).grading (FusionColumn.grading (Γ.fuse p q))
            (gTCanon K Γ (p + q) r s).toLinearMap (gParity K Γ (p + q) r s)
            (gCanonHphi4 K Γ p q r s)) (gq1Assoc K Γ p q r s m))
  rw [gq1Assoc_rightTotal]
  exact LinearMap.congr_fun
    (smap_comp_rightActionEnd (Γ.D (p + q)).grading (FusionColumn.grading (Γ.fuse p q))
      (gTCanon K Γ (p + q) r s).toLinearMap (gParity K Γ (p + q) r s) (gCanonHphi4 K Γ p q r s)
      (gCanonRight K Γ (p + q) r s τ))
    (gq1Assoc K Γ p q r s m)

/-! ### The 21 edge maps: landed this round -/

/-- **Edge 1** `E1M : V1 → V2`, `t_{a,b,c}|d|e` (owning faces `P6`, `S1`;
presentation chosen: `P6`, the whiskered `GE1` at the FIXED
`gTCanon Γ a b c`). -/
noncomputable def E1M : V1 K Γ a b c d e →ₗ[K] V2 K Γ a b c d e :=
  RelTensor.map (GE1 K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
    LinearMap.id (GE1_rightTotal K Γ a b c d) (fun _ _ => rfl)

theorem E1M_bijective : Function.Bijective (E1M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE1 K Γ a b c d (gTCanon K Γ a b c).toLinearMap (gCanonRight K Γ a b c))
      (PentagonB.RelTensor.map_bijective_left K (gTCanon K Γ a b c) (gCanonRight K Γ a b c)))
    (GE1_rightTotal K Γ a b c d)

/-- **Edge 3** `E3M : V4 → V5`, `t_{b,c,d}|e` (owning faces `P6`, `S2`;
presentation: `P6`, the whiskered `GE3` at the FIXED `gTCanon Γ b c d`). -/
noncomputable def E3M : V4 K Γ a b c d e →ₗ[K] V5 K Γ a b c d e :=
  RelTensor.map (GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
    LinearMap.id (GE3_rightTotal K Γ a b c d) (fun _ _ => rfl)

theorem E3M_bijective : Function.Bijective (E3M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE3 K Γ a b c d (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
      ((PentagonB.RelTensor.map_bijective_left K (gTCanon K Γ b c d) (gCanonRight K Γ b c d)).comp
        (gq3Assoc K Γ a b c d).symm.bijective))
    (GE3_rightTotal K Γ a b c d)

/-- **Edge 6** `E6M : V10 → V11`, `a|t_{b,c,d}|e` (owning faces `P1`,
`S2`; presentation: `P1`, the `V10..V14`-mirror of `GE1`, at the FIXED
`gTCanon Γ b c d`). -/
noncomputable def E6M : V10 K Γ a b c d e →ₗ[K] V11 K Γ a b c d e :=
  RelTensor.map (GE1 K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
    LinearMap.id (GE1_rightTotal K Γ b c d e) (fun _ _ => rfl)

theorem E6M_bijective : Function.Bijective (E6M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE1 K Γ b c d e (gTCanon K Γ b c d).toLinearMap (gCanonRight K Γ b c d))
      (PentagonB.RelTensor.map_bijective_left K (gTCanon K Γ b c d) (gCanonRight K Γ b c d)))
    (GE1_rightTotal K Γ b c d e)

/-- **Edge 8** `E8M : V13 → V14`, `a|b|t_{c,d,e}` (owning faces `P1`,
`S3`; presentation: `P1`, the `V10..V14`-mirror of `GE3`, at the FIXED
`gTCanon Γ c d e`). -/
noncomputable def E8M : V13 K Γ a b c d e →ₗ[K] V14 K Γ a b c d e :=
  RelTensor.map (GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e))
    LinearMap.id (GE3_rightTotal K Γ b c d e) (fun _ _ => rfl)

theorem E8M_bijective : Function.Bijective (E8M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE3 K Γ b c d e (gTCanon K Γ c d e).toLinearMap (gCanonRight K Γ c d e))
      ((PentagonB.RelTensor.map_bijective_left K (gTCanon K Γ c d e) (gCanonRight K Γ c d e)).comp
        (gq3Assoc K Γ b c d e).symm.bijective))
    (GE3_rightTotal K Γ b c d e)

/-! ### Edge 12: `E12M : V8 → V9`, `(a+b)|t_{c,d,e}` (owning faces `PAB`,
`S3`; presentation: `S3`). **M13-1′ re-landing**, past the `V8`/`V9` fix
(`Quint.lean`): `V8 = F_{a,b} ⊗_{D_{a+b}} V8Inner`, so `E12M` is `id_{F_{a,b}}`
whiskered over the OLD `E12M` (now `E12MInnerEquiv`, the map `V8Inner →
V9Inner`) — via `smap`/`PentagonB.smapEquiv`, NOT plain `RelTensor.map`
(the previous round's obstruction): `gTCanon Γ c d e` is generically ODD
(`gParity K Γ c d e` need not vanish), so `E12MInnerEquiv` is only
SIGNED-equivariant for the new `(a+b)`-slot action on `V8Inner`/`V9Inner`
(`Quint.lean`'s `map_comm_midEndFirst`, the `midEnd` analogue of the
square lemma) — exactly `smap`'s own hypothesis shape, dissolving the
obstruction. -/

/-- The old `E12M`, now the map `V8Inner → V9Inner` (a bare whiskered
`gTCanon Γ c d e` on the top-level `GBL`/`GBR` factor), packaged as a
`LinearEquiv` (`PentagonB.RelTensor.mapEquivLeft`, needed to feed
`PentagonB.smapEquiv` below). -/
noncomputable def E12MInnerEquiv : V8Inner K Γ a b c d e ≃ₗ[K] V9Inner K Γ a b c d e :=
  PentagonB.RelTensor.mapEquivLeft K (gTCanon K Γ c d e) (gCanonRight K Γ c d e)

theorem E12MInnerEquiv_toLinearMap :
    (E12MInnerEquiv K Γ a b c d e).toLinearMap
      = RelTensor.map (gTCanon K Γ c d e).toLinearMap LinearMap.id (gCanonRight K Γ c d e)
          (fun _ _ => rfl) :=
  PentagonB.RelTensor.mapEquivLeft_toLinearMap K (gTCanon K Γ c d e) (gCanonRight K Γ c d e)

/-- `gTCanon Γ c d e`'s own degree, restated (`gInterSpace`'s `homGrading`
conjunct — the public re-statement mirroring `gCanonRight`). -/
theorem gCanonDeg (x y z : G) :
    (gTCanon K Γ x y z).toLinearMap ∈
      homGrading (GBL.grading Γ x y z) (GBR.grading Γ x y z) (gParity K Γ x y z) :=
  ((mem_gInterSpace_iff K Γ x y z).mp (gTCanon_mem_gInterSpace K Γ x y z)).1

/-- **`E12MInnerEquiv`'s signed `(a+b)`-slot equivariance**: the `midEnd`
square lemma (`map_comm_midEndFirst`), specialized at the `(a+b)`-slot
`midEnd` action on `V8Inner`/`V9Inner` (`Quint.lean`'s
`instModuleV8InnerASlot`/`instModuleV9InnerASlot`, both built from the
SAME `superCommSMul_symm (Γ.D (a+b)).grading (Γ.D (c+d+e)).grading
(FusionColumn.superCommSMul (Γ.fuse (a+b) (c+d+e)))` witness). -/
theorem E12MInnerEquiv_aSlot :
    ∀ ⦃i : ZMod 2⦄ ⦃τ : (Γ.D (a + b)).carrier⦄,
      τ ∈ (Γ.D (a + b)).grading i → ∀ n : V8Inner K Γ a b c d e,
        E12MInnerEquiv K Γ a b c d e (τ • n)
          = ((sgn (gParity K Γ c d e * i) : ℤˣ) : ℤ) •
              (τ • E12MInnerEquiv K Γ a b c d e n) := by
  intro i τ hτ n
  set hsc := superCommSMul_symm (Γ.D (a + b)).grading (Γ.D (c + d + e)).grading
    (FusionColumn.superCommSMul (Γ.fuse (a + b) (c + d + e)))
  -- ONE big `show`, unfolding `E12MInnerEquiv`/the `(a+b)`-slot `•` to their raw
  -- `RelTensor.map`/`midEnd` spellings in a single defeq check (default transparency,
  -- never crossing a `rw`/`Eq.mpr` motive at the "instances" transparency level that
  -- the `def`-wrapped `V8Inner`/`V9Inner` trap needs to be avoided).
  show RelTensor.map (gTCanon K Γ c d e).toLinearMap LinearMap.id (gCanonRight K Γ c d e)
        (fun _ _ => rfl)
      (midEnd (Γ.D (c + d + e)).grading (GBL.grading Γ c d e) (Γ.D (a + b)).grading hsc τ n)
    = ((sgn (gParity K Γ c d e * i) : ℤˣ) : ℤ) •
        midEnd (Γ.D (c + d + e)).grading (GBR.grading Γ c d e) (Γ.D (a + b)).grading hsc τ
          (RelTensor.map (gTCanon K Γ c d e).toLinearMap LinearMap.id (gCanonRight K Γ c d e)
            (fun _ _ => rfl) n)
  simpa using LinearMap.congr_fun
    (map_comm_midEndFirst (𝒜 := (Γ.D (c + d + e)).grading)
      (ℳ := GBL.grading Γ c d e) (ℳ' := GBR.grading Γ c d e) (𝒞 := (Γ.D (a + b)).grading)
      (hsc := hsc) (hsc' := hsc) (f := (gTCanon K Γ c d e).toLinearMap)
      (hf := gCanonRight K Γ c d e) (hfdeg := gCanonDeg K Γ c d e) (hc := hτ)) n

/-- **`E12M`, as a `LinearEquiv`**: `id_{F_{a,b}}` whiskered (`smap`)
over `E12MInnerEquiv`. -/
noncomputable def E12Mequiv : V8 K Γ a b c d e ≃ₗ[K] V9 K Γ a b c d e :=
  PentagonB.smapEquiv K (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
    (E12MInnerEquiv K Γ a b c d e) (gParity K Γ c d e) (E12MInnerEquiv_aSlot K Γ a b c d e)

noncomputable def E12M : V8 K Γ a b c d e →ₗ[K] V9 K Γ a b c d e :=
  (E12Mequiv K Γ a b c d e).toLinearMap

theorem E12M_bijective : Function.Bijective (E12M K Γ a b c d e) :=
  (E12Mequiv K Γ a b c d e).bijective

/-- **Edge 20** `E20M : V6 → V7`, `t_{a,b,c}|(d+e)` (owning faces `PDE`,
`S1`; presentation: `S1`, the SIMPLEST genre — a bare whiskered
`gTCanon Γ a b c` directly on `V6`/`V7`'s own top-level `GBL`/`GBR`
factor, no `GQ`-`Total` layer at all). -/
noncomputable def E20M : V6 K Γ a b c d e →ₗ[K] V7 K Γ a b c d e :=
  RelTensor.map (gTCanon K Γ a b c).toLinearMap LinearMap.id (gCanonRight K Γ a b c)
    (fun _ _ => rfl)

theorem E20M_bijective : Function.Bijective (E20M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K (gTCanon K Γ a b c) (gCanonRight K Γ a b c)

/-- **Edge 4** `E4M : V1 → V3`, `t_{a+b,c,d}|e` (owning faces `P6`,
`PAB`; presentation: `P6`, the whiskered `GE4` at the FIXED
`gTCanon Γ (a+b) c d`). -/
noncomputable def E4M : V1 K Γ a b c d e →ₗ[K] V3 K Γ a b c d e :=
  RelTensor.map (GE4 K Γ a b c d (gParity K Γ (a + b) c d)
      (gTCanon K Γ (a + b) c d).toLinearMap (gCanonHphi4 K Γ a b c d))
    LinearMap.id (GE4_rightTotal K Γ a b c d) (fun _ _ => rfl)

theorem E4M_bijective : Function.Bijective (E4M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE4 K Γ a b c d (gParity K Γ (a + b) c d) (gTCanon K Γ (a + b) c d).toLinearMap
        (gCanonHphi4 K Γ a b c d))
      ((PentagonB.smap_bijective K (Γ.D (a + b)).grading (FusionColumn.grading (Γ.fuse a b))
          (gTCanon K Γ (a + b) c d) (gParity K Γ (a + b) c d) (gCanonHphi4 K Γ a b c d)).comp
        (gq1Assoc K Γ a b c d).bijective))
    (GE4_rightTotal K Γ a b c d)

/-- **Edge 9** `E9M : V10 → V12`, `a|t_{b+c,d,e}` (owning faces `P1`,
`PBC`; presentation: `P1`, the `V10..V14`-mirror of `GE4`, at the FIXED
`gTCanon Γ (b+c) d e`). -/
noncomputable def E9M : V10 K Γ a b c d e →ₗ[K] V12 K Γ a b c d e :=
  RelTensor.map (GE4 K Γ b c d e (gParity K Γ (b + c) d e)
      (gTCanon K Γ (b + c) d e).toLinearMap (gCanonHphi4 K Γ b c d e))
    LinearMap.id (GE4_rightTotal K Γ b c d e) (fun _ _ => rfl)

theorem E9M_bijective : Function.Bijective (E9M K Γ a b c d e) :=
  PentagonB.RelTensor.map_bijective_left K
    (LinearEquiv.ofBijective
      (GE4 K Γ b c d e (gParity K Γ (b + c) d e) (gTCanon K Γ (b + c) d e).toLinearMap
        (gCanonHphi4 K Γ b c d e))
      ((PentagonB.smap_bijective K (Γ.D (b + c)).grading (FusionColumn.grading (Γ.fuse b c))
          (gTCanon K Γ (b + c) d e) (gParity K Γ (b + c) d e) (gCanonHphi4 K Γ b c d e)).comp
        (gq1Assoc K Γ b c d e).bijective))
    (GE4_rightTotal K Γ b c d e)

end GaugeChi

end Superfusion
