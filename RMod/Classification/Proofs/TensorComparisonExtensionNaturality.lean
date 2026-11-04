import RMod.Classification.Proofs.TensorComparisonExtensionGenerator
import RMod.Classification.Proofs.SpanTensor

/-!
# Full signed naturality of the extended tensor comparison

Test both sides after the mapped inclusions of the source tensor
presentation. The generator equation applies to the two composites.
Super-interchange supplies matching crossing signs on both sides, and
the parity-power addition law accounts for the naturality sign.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

variable {C D : WeaklyPointedSuperfusion.{0, 0}}
  {S T : SimpleObject C} {U V : SimpleObject D}
  {E : SpanSuperfunctor C D S.data.object U.data.object}
  {H : SpanSuperfunctor C D T.data.object V.data.object}
  {N : SpanSuperfunctor C D (simpleTensorRepresentative C S T).data.object
    (simpleTensorRepresentative D U V).data.object} {a : ZMod 2}
  (t : TensorIntertwiner S T U V E H N a)

theorem tensorComparisonExtension_naturality
    {X X' : HomogeneousSpanCategory C S.data.object} {Y Y' : HomogeneousSpanCategory C T.data.object}
    {b c : ZMod 2} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : C.data.IsHomogeneous b f.hom) (hg : C.data.IsHomogeneous c g.hom) :
    D.data.comp (N.data.map (spanTensorHom C S T f g)).hom
      ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X' Y').hom =
    D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
      (D.data.comp ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X Y).hom
        (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)) := by
  let d := tensorComparisonSourcePresentation S T U V N X Y
  apply hom_ext_of_inclusions D.laws d.data.inclusion d.data.projection d.laws.total
  intro i
  let j := (finProdFinEquiv.symm i).1
  let k := (finProdFinEquiv.symm i).2
  let p : spanGenerator C S.data.object ⟶ X := ObjectProperty.homMk ((spanPresentation X).data.inclusion j)
  let q : spanGenerator C T.data.object ⟶ Y := ObjectProperty.homMk ((spanPresentation Y).data.inclusion k)
  let u := (spanPresentation X).data.parity j
  let v := (spanPresentation Y).data.parity k
  have hp : C.data.IsHomogeneous u p.hom := (spanPresentation X).laws.inclusion_grade j
  have hq : C.data.IsHomogeneous v q.hom := (spanPresentation Y).laws.inclusion_grade k
  have hl := tensorComparisonExtension_on_generator_hom t (p ≫ f) (q ≫ g)
    (C.laws.comp_grade _ _ hp hf) (C.laws.comp_grade _ _ hq hg)
  have hr := tensorComparisonExtension_on_generator_hom t p q hp hq
  have hm := map_spanTensorHom_comp S T N p q f g hg hp
  have hemap := congrArg (fun w : E.data.obj (spanGenerator C S.data.object) ⟶ E.data.obj X' => w.hom)
    (E.laws.map_comp p f)
  have hhmap := congrArg (fun w : H.data.obj (spanGenerator C T.data.object) ⟶ H.data.obj Y' => w.hom)
    (H.laws.map_comp q g)
  change (E.data.map (p ≫ f)).hom = D.data.comp (E.data.map p).hom (E.data.map f).hom at hemap
  change (H.data.map (q ≫ g)).hom = D.data.comp (H.data.map q).hom (H.data.map g).hom at hhmap
  change D.data.comp (N.data.map (spanTensorHom C S T p q)).hom
    (D.data.comp (N.data.map (spanTensorHom C S T f g)).hom
      ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X' Y').hom) =
    D.data.comp (N.data.map (spanTensorHom C S T p q)).hom
      (D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
        (D.data.comp ((tensorComparisonExtensionData S T U V E.data H.data N.data a t.data).app X Y).hom
          (D.data.tensorHom (E.data.map f).hom (H.data.map g).hom)))
  rw [← D.laws.comp_assoc, hm, D.laws.smul_comp, hl, D.laws.comp_smul,
    ← D.laws.comp_assoc, hr]
  let l₁ := D.data.tensorHom (E.data.map p).hom (H.data.map q).hom
  let l₂ := D.data.tensorHom (E.data.map f).hom (H.data.map g).hom
  let l₃ := D.data.tensorHom (E.data.map (p ≫ f)).hom (H.data.map (q ≫ g)).hom
  have htensor : D.data.comp l₁ l₂ = D.data.smul ((-1 : ℝ) ^ (c * u).val) l₃ :=
    (D.laws.super_interchange _ _ _ _ (H.laws.map_grade g hg) (E.laws.map_grade p hp)).trans
      (congrArg (D.data.smul ((-1 : ℝ) ^ (c * u).val))
        (congrArg₂ (fun x y => D.data.tensorHom x y) hemap.symm hhmap.symm))
  change D.data.smul ((-1 : ℝ) ^ (c * u).val)
    (D.data.smul ((-1 : ℝ) ^ (a * ((u + b) + (v + c))).val) (D.data.comp t.data.hom l₃)) =
    D.data.smul ((-1 : ℝ) ^ (a * (b + c)).val)
      (D.data.comp (D.data.smul ((-1 : ℝ) ^ (a * (u + v)).val) (D.data.comp t.data.hom l₁)) l₂)
  rw [D.laws.smul_comp, D.laws.comp_assoc, htensor, D.laws.comp_smul]
  have hdeg : (u + b) + (v + c) = (b + c) + (u + v) := by abel
  rw [hdeg, mul_add, parity_power_add]
  simp only [← D.laws.mul_smul]
  congr 1
  ring

theorem tensorComparisonExtensionLaws : TensorComparisonLaws S T U V a
    (tensorComparisonExtensionData S T U V E.data H.data N.data a t.data) where
  iso := tensorComparisonExtension_iso t
  hom_grade := tensorComparisonExtension_hom_grade t
  inv_grade := tensorComparisonExtension_inv_grade t
  naturality f g hf hg := tensorComparisonExtension_naturality t f g hf hg

end RMod.Classification
