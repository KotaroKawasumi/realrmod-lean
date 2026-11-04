import RMod.Hierarchy.Instances.HomogeneousOperations
import RMod.Hierarchy.Instances.TensorInterchangePoints

/-!
# Super-interchange on total homogeneous morphisms

The tensor superfunctor preserves composition in the enriched product.
Evaluating its composition law on four homogeneous generators exposes the
single Koszul crossing of the middle two factors.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace RMod.Legacy
variable (C : MonoidalSupercategory)

theorem componentTensor_interchange {X X' X'' Y Y' Y'' : C.data.Obj}
    (i j k l n : ZMod 2) (h : i + j + k + l = n)
    (f : C.data.Hom X X' i) (g : C.data.Hom Y Y' j)
    (q : C.data.Hom X' X'' k) (r : C.data.Hom Y' Y'' l) :
    C.data.comp _ _ _ n
      (gradedTmul _ _ (i + j) (k + l) n (by rw [← add_assoc, h])
        (C.data.monoidal.tensor.map (X, Y) (X', Y') (i + j)
          (gradedTmul _ _ i j (i + j) rfl f g))
        (C.data.monoidal.tensor.map (X', Y') (X'', Y'') (k + l)
          (gradedTmul _ _ k l (k + l) rfl q r))) =
    (-1 : ℝ) ^ (j * k).val • C.data.monoidal.tensor.map (X, Y) (X'', Y'') n
      (gradedTmul _ _ (i + k) (j + l) n (by linear_combination h)
        (C.data.comp X X' X'' (i + k) (gradedTmul _ _ i k (i + k) rfl f q))
        (C.data.comp Y Y' Y'' (j + l) (gradedTmul _ _ j l (j + l) rfl g r))) := by
  let A := C.data.Hom X X'
  let B := C.data.Hom Y Y'
  let D := C.data.Hom X' X''
  let E := C.data.Hom Y' Y''
  let v := gradedTmul (A ⊗ B) (D ⊗ E) (i + j) (k + l) n
    (by rw [← add_assoc, h])
    (gradedTmul A B i j (i + j) rfl f g) (gradedTmul D E k l (k + l) rfl q r)
  have he := congrArg (fun m => m n v)
    (C.laws.monoidal.tensor.map_comp (X, Y) (X', Y') (X'', Y''))
  change C.data.monoidal.tensor.map (X, Y) (X'', Y'') n
      ((C.data.comp X X' X'' ⊗ₘ C.data.comp Y Y' Y'') n (tensorμ A B D E n v)) =
    C.data.comp _ _ _ n
      ((C.data.monoidal.tensor.map (X, Y) (X', Y') ⊗ₘ
        C.data.monoidal.tensor.map (X', Y') (X'', Y'')) n v) at he
  dsimp only [v] at he
  erw [tensorμ_gradedTmul A B D E i j k l n h, map_smul,
    tensorHom_gradedTmul, map_smul, tensorHom_gradedTmul] at he
  exact he.symm

theorem tTensor_interchange {X X' X'' Y Y' Y'' : C.data.Obj}
    (i j k l : ZMod 2)
    (f : THom C.super.data X X') (g : THom C.super.data Y Y')
    (q : THom C.super.data X' X'') (r : THom C.super.data Y' Y'')
    (hf : f ∈ grade C.super X X' i) (hg : g ∈ grade C.super Y Y' j)
    (hq : q ∈ grade C.super X' X'' k) (hr : r ∈ grade C.super Y' Y'' l) :
    tComp C.super.data (tTensor C.data.monoidal f g) (tTensor C.data.monoidal q r) =
      (-1 : ℝ) ^ (j * k).val •
        tTensor C.data.monoidal (tComp C.super.data f q) (tComp C.super.data g r) := by
  have hfg := tTensor_mem_grade C.super C.data.monoidal f g hf hg
  have hqr := tTensor_mem_grade C.super C.data.monoidal q r hq hr
  have hfq := tComp_mem_grade C.super f q hf hq
  have hgr := tComp_mem_grade C.super g r hg hr
  have hd : (i + k) + (j + l) = (i + j) + (k + l) := by abel
  have ht := tTensor_mem_grade C.super C.data.monoidal
    (tComp C.super.data f q) (tComp C.super.data g r) hfq hgr
  rw [hd] at ht
  apply homogeneous_ext C.super (tComp_mem_grade C.super _ _ hfg hqr)
    ((grade C.super _ _ _).smul_mem _ ht)
  change tComp C.super.data _ _ ((i + j) + (k + l)) =
    (-1 : ℝ) ^ (j * k).val • tTensor C.data.monoidal _ _ ((i + j) + (k + l))
  rw [tComp_homogeneous_at C.super (i + j) (k + l) _ rfl _ _ hfg,
    tTensor_homogeneous_at C.super C.data.monoidal i j _ rfl f g hf,
    tTensor_homogeneous_at C.super C.data.monoidal k l _ rfl q r hq,
    tTensor_homogeneous_at C.super C.data.monoidal (i + k) (j + l) _ hd _ _ hfq,
    tComp_homogeneous_at C.super i k _ rfl f q hf,
    tComp_homogeneous_at C.super j l _ rfl g r hg]
  exact componentTensor_interchange C i j k l _ (add_assoc (i + j) k l)
    (f i) (g j) (q k) (r l)

end RMod.Legacy
