import RMod.Hierarchy.Bridge.LegacyTensor
import RMod.Hierarchy.Bridge.TensorComponents
import RMod.Hierarchy.Bridge.MonoidalLaws
import RMod.Hierarchy.Instances.EquivalenceFunctors

/-!
# Tensor naturality in the legacy convention

The total Hom equivalence sends the convention-corrected enriched tensor
to the original tensor. Degreewise functors commute with the odd projection,
so enriched tensor naturality also holds after the correction.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.Legacy.Hierarchy

theorem totalHomEquiv_legacyTensor (C : WeaklyPointedSuperfusion.{0, 0})
    {X X' Y Y' : C.data.Obj} (f : THom (ofOldSupercategoryData C) X X')
    (g : THom (ofOldSupercategoryData C) Y Y') :
    totalHomEquiv C _ _ (legacyTensor (ofOldMonoidalSupercategory C) f g) =
      C.data.tensorHom (totalHomEquiv C X X' f) (totalHomEquiv C Y Y' g) := by
  let U : Classification.LinearCategory C := C.data.tensorObj X Y
  let V : Classification.LinearCategory C := C.data.tensorObj X' Y'
  letI : AddCommGroup (C.data.Hom U V) := inferInstanceAs (AddCommGroup (U ⟶ V))
  letI : Module ℝ (C.data.Hom U V) := inferInstanceAs (Module ℝ (U ⟶ V))
  unfold legacyTensor
  erw [map_sub, map_smul, totalHomEquiv_tTensor, totalHomEquiv_tTensor]
  have hf₀ : (homogeneousPart (ofOldMonoidalSupercategory C).super 1 f 0).val = C.data.zero := rfl
  have hg₀ : (homogeneousPart (ofOldMonoidalSupercategory C).super 1 g 0).val = C.data.zero := rfl
  have hf₁ : (homogeneousPart (ofOldMonoidalSupercategory C).super 1 f 1).val = (f 1).val := rfl
  have hg₁ : (homogeneousPart (ofOldMonoidalSupercategory C).super 1 g 1).val = (g 1).val := rfl
  simp only [hf₀, hg₀, hf₁, hg₁]
  simp only [Classification.tensor_zero_left C.laws, Classification.tensor_zero_right C.laws,
    C.laws.zero_add, C.laws.add_zero, totalHomEquiv_apply,
    C.laws.tensor_add_left, C.laws.tensor_add_right]
  change (C.data.tensorHom (f 0).val (g 0).val + (-1 : ℝ) • C.data.tensorHom (f 1).val (g 1).val) +
    (C.data.tensorHom (f 0).val (g 1).val + C.data.tensorHom (f 1).val (g 0).val) -
    (2 : ℝ) • ((-1 : ℝ) • C.data.tensorHom (f 1).val (g 1).val) =
    (C.data.tensorHom (f 0).val (g 0).val + C.data.tensorHom (f 0).val (g 1).val) +
    (C.data.tensorHom (f 1).val (g 0).val + C.data.tensorHom (f 1).val (g 1).val)
  simp only [neg_one_smul, two_smul ℝ]
  abel

theorem tMap_homogeneousPart {C D : Supercategory} (F : Superfunctor C D)
    {X Y : C.data.Obj} (a : ZMod 2) (f : THom C.data X Y) :
    tMap F.data (homogeneousPart C a f) = homogeneousPart D a (tMap F.data f) := by
  funext b
  by_cases hb : b = a
  · simp [homogeneousPart, tMap, hb]
  · simp [homogeneousPart, tMap, hb]

theorem legacyTensor_natural {C D : MonoidalSupercategory} (E : MonoidalSuperequivalence C D)
    {X X' Y Y' : C.data.Obj} (f : THom C.super.data X X') (g : THom C.super.data Y Y') :
    tComp D.super.data (legacyTensor D (tMap E.data.forward f) (tMap E.data.forward g))
      (evenPoint (E.data.tensorIso X' Y').hom) =
    tComp D.super.data (evenPoint (E.data.tensorIso X Y).hom)
      (tMap E.data.forward (legacyTensor C f g)) := by
  have h₀ := E.laws.tensor_natural f g
  have h₁ := E.laws.tensor_natural (homogeneousPart C.super 1 f) (homogeneousPart C.super 1 g)
  erw [tMap_homogeneousPart E.forward, tMap_homogeneousPart E.forward] at h₁
  have h := congrArg₂ (fun a b : THom D.super.data _ _ => a - (2 : ℝ) • b) h₀ h₁
  have hsub {S T U : D.super.data.Obj} (a b : THom D.super.data S T) (c : THom D.super.data T U) :
      tComp D.super.data (a - b) c = tComp D.super.data a c - tComp D.super.data b c := by
    rw [sub_eq_add_neg, ← neg_one_smul ℝ b, tComp_add_left, tComp_smul_left, neg_one_smul, ← sub_eq_add_neg]
  have hsub' {S T U : D.super.data.Obj} (a : THom D.super.data S T) (b c : THom D.super.data T U) :
      tComp D.super.data a (b - c) = tComp D.super.data a b - tComp D.super.data a c := by
    rw [sub_eq_add_neg, ← neg_one_smul ℝ c, tComp_add_right, tComp_smul_right, neg_one_smul, ← sub_eq_add_neg]
  have hm {S T : C.super.data.Obj} (a b : THom C.super.data S T) :
      tMap E.data.forward (a - b) = tMap E.data.forward a - tMap E.data.forward b := by
    erw [sub_eq_add_neg, ← neg_one_smul ℝ b, tMap_add E.forward, tMap_smul E.forward, neg_one_smul, ← sub_eq_add_neg]
    rfl
  let u := tTensor D.data.monoidal (tMap E.data.forward f) (tMap E.data.forward g)
  let v := tTensor D.data.monoidal (homogeneousPart D.super 1 (tMap E.data.forward f))
    (homogeneousPart D.super 1 (tMap E.data.forward g))
  let r := tTensor C.data.monoidal f g
  let s := tTensor C.data.monoidal (homogeneousPart C.super 1 f) (homogeneousPart C.super 1 g)
  let w := evenPoint (E.data.tensorIso X' Y').hom
  let z := evenPoint (E.data.tensorIso X Y).hom
  change tComp D.super.data (u - (2 : ℝ) • v) w =
    tComp D.super.data z (tMap E.data.forward (r - (2 : ℝ) • s))
  erw [hsub u ((2 : ℝ) • v) w, tComp_smul_left D.super.data 2 v w,
    hm r ((2 : ℝ) • s), tMap_smul E.forward 2 s,
    hsub' z (tMap E.data.forward r) ((2 : ℝ) • tMap E.data.forward s),
    tComp_smul_right D.super.data 2 z (tMap E.data.forward s)]
  exact h

end RMod.Legacy.Hierarchy
