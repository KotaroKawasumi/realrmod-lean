/-
Superfusion / GaugeChi / QuadChaseNativeExpansion

Finite generator expansions for the two ternary route carriers.

The native fourfold checker evaluates explicit matrix columns.  To connect
that evaluation to the quotient-defined pentagon edges, an arbitrary `GBL`
or `GBR` element is expanded in the same finite frame: the first fusion
column is a unit singleton and the whole coefficient is placed in the
second singleton.  Applying the corresponding column dictionary turns the
claim into the elementary expansion of a finite function by singletons.
-/
import Superfusion.GaugeChi.QuadChaseNative

set_option autoImplicit false

namespace Superfusion
namespace GaugeChi

open scoped TensorProduct
open Bimod

universe u v

section Expansion

variable (K : Type u) [Field K] [Invertible (2 : K)]
variable {G : Type v} [AddGroup G]
variable (Gamma : DivisionFusionGauge K G)
variable (a b c : G)

attribute [local instance 500] leftModule rightModule

/-- A finite function is the sum of its singleton columns. -/
private theorem sum_fsingle_eq
    {P B : SuperAlgebra K} {p q : Nat}
    (phi : SuperAlgEquiv P (B.matrixSuper p q))
    (w : FusionColumn phi) :
    (∑ x : Fin p ⊕ Fin q, fsingle phi x (w x)) = w := by
  classical
  funext y
  have hsum :
      ((∑ x : Fin p ⊕ Fin q, fsingle phi x (w x)) : FusionColumn phi) y =
        ∑ x : Fin p ⊕ Fin q, (fsingle phi x (w x) : FusionColumn phi) y :=
    Finset.sum_apply y Finset.univ (fun x => fsingle phi x (w x))
  rw [hsum]
  simp only [fsingle_apply]
  rw [Finset.sum_eq_single y]
  · rw [if_pos rfl]
  · intro z _ hz
    rw [if_neg fun hy => hz hy.symm]
  · intro hy
    exact absurd (Finset.mem_univ y) hy

/-- The same singleton expansion after identifying the row type with a
finite product.  This is the reindexing used by both ternary dictionaries. -/
private theorem sum_fsingle_equiv_prod_eq
    {P B : SuperAlgebra K} {p q : Nat} {I J : Type*}
    [Fintype I] [Fintype J]
    (phi : SuperAlgEquiv P (B.matrixSuper p q))
    (e : I × J ≃ Fin p ⊕ Fin q)
    (w : FusionColumn phi) :
    (∑ i : I, ∑ j : J, fsingle phi (e (i, j)) (w (e (i, j)))) = w := by
  classical
  funext y
  have houter :
      ((∑ i : I, ∑ j : J, fsingle phi (e (i, j)) (w (e (i, j)))) :
          FusionColumn phi) y =
        ∑ i : I, ((∑ j : J, fsingle phi (e (i, j)) (w (e (i, j)))) :
          FusionColumn phi) y :=
    Finset.sum_apply y Finset.univ (fun i =>
      ∑ j : J, fsingle phi (e (i, j)) (w (e (i, j))))
  rw [houter]
  have hinner (i : I) :
      ((∑ j : J, fsingle phi (e (i, j)) (w (e (i, j)))) :
          FusionColumn phi) y =
        ∑ j : J, (fsingle phi (e (i, j)) (w (e (i, j))) : FusionColumn phi) y :=
    Finset.sum_apply y Finset.univ (fun j =>
      fsingle phi (e (i, j)) (w (e (i, j))))
  simp_rw [hinner, fsingle_apply]
  let ij := e.symm y
  rw [Finset.sum_eq_single ij.1]
  · rw [Finset.sum_eq_single ij.2]
    · rw [if_pos (by simp [ij])]
      simp [ij]
    · intro j _ hj
      rw [if_neg]
      intro hy
      have hp : ij = (ij.1, j) := by
        simpa [ij] using congrArg e.symm hy
      exact hj (congrArg Prod.snd hp).symm
    · intro hij
      exact absurd (Finset.mem_univ ij.2) hij
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    intro hy
    have hp : ij = (i, j) := by
      simpa [ij] using congrArg e.symm hy
    exact hi (congrArg Prod.fst hp).symm
  · intro hij
    exact absurd (Finset.mem_univ ij.1) hij

/-- Every left-associated ternary route element is a finite sum of pure
singleton generators in the parity-aligned left frame. -/
theorem gbl_eq_sum_mk_fsingle (m : GBL Gamma a b c) :
    m =
      ∑ l : Fin (Gamma.size a b).1 ⊕ Fin (Gamma.size a b).2,
        ∑ r : Fin (Gamma.size (a + b) c).1 ⊕
            Fin (Gamma.size (a + b) c).2,
          GBL.mk Gamma a b c
            (fsingle (Gamma.fuse a b) l 1)
            (fsingle (Gamma.fuse (a + b) c) r
              ((gblColumnEquiv K Gamma a b c m :
                  FusionColumn (Gamma.gaugeRouteL a b c))
                (gblIndexEquiv K Gamma a b c (l, r)))) := by
  classical
  apply (gblColumnEquiv K Gamma a b c).injective
  simp_rw [map_sum, gblColumnEquiv_fsingle]
  exact (sum_fsingle_equiv_prod_eq K (Gamma.gaugeRouteL a b c)
    (gblIndexEquiv K Gamma a b c)
    (gblColumnEquiv K Gamma a b c m)).symm

/-- Every right-associated ternary route element is a finite sum of pure
singleton generators in its native (possibly rectangular) right frame. -/
theorem gbr_eq_sum_mk_fsingle_native (m : GBR Gamma a b c) :
    m =
      ∑ l : Fin (Gamma.size b c).1 ⊕ Fin (Gamma.size b c).2,
        ∑ r : Fin (Gamma.size a (b + c)).1 ⊕
            Fin (Gamma.size a (b + c)).2,
          GBR.mk Gamma a b c
            (fsingle (Gamma.fuse b c) l 1)
            (fsingle (Gamma.fuse a (b + c)) r
              ((gbrNativeColumnEquiv K Gamma a b c m :
                  FusionColumn (Gamma.gaugeRouteR a b c))
                (gbrNativeIndexEquiv K Gamma a b c (l, r)))) := by
  classical
  apply (gbrNativeColumnEquiv K Gamma a b c).injective
  simp_rw [map_sum, gbrNativeColumnEquiv_fsingle]
  exact (sum_fsingle_equiv_prod_eq K (Gamma.gaugeRouteR a b c)
    (gbrNativeIndexEquiv K Gamma a b c)
    (gbrNativeColumnEquiv K Gamma a b c m)).symm

end Expansion

end GaugeChi
end Superfusion
