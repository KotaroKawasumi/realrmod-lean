import RMod.Classification.Instances.ConvolutionComponentReindex
import RMod.Classification.Proofs.ConvolutionComponentComparison
import RMod.Classification.Proofs.IndexedMorphismEquality

/-!
# Reindexing retains the comparison's degree and signed naturality

The added map is the even equality isomorphism on the right input index.
Naturality of indexed morphisms keeps this equality map in both routes.
-/

set_option autoImplicit false

namespace RMod.Classification

variable (C : PiSuperfusionData.{0, 0}) (hC : ReferenceProperty C) (t : TwistData)

theorem convolutionComponentReindex_homogeneousIso
    (X Y : PullbackObj C t) (k g h : t.group) (e : g⁻¹ * k = h)
    (hX : ∀ l, l ≠ g → C.id (X l).val = C.zero) :
    HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData (t.nu g h)
      (convolutionComponentReindexData C hC t X Y k g h e) := by
  have hi := (convolutionComponentComparison_homogeneousIso C hC t X Y k g hX).trans
    hC.toWeaklyPointedSuperfusionLaws
    ((EvenIsoLaws.ofEq hC.toWeaklyPointedSuperfusionLaws
      (congrArg (fun l => C.tensorObj (X g).val (Y l).val) e)).homogeneous)
  rw [add_zero] at hi
  exact Eq.mp (congrArg (fun a => HomogeneousIsoLaws C.toWeaklyPointedSuperfusionData a
    (convolutionComponentReindexData C hC t X Y k g h e)) (congrArg (t.nu g) e)) hi

theorem convolutionComponentReindex_naturality
    {X X' Y Y' : PullbackObj C t} {a b : ZMod 2}
    (f : PullbackHom C t X X') (q : PullbackHom C t Y Y')
    (hf : ∀ k, C.IsHomogeneous a (f k)) (hq : ∀ k, C.IsHomogeneous b (q k))
    (k g h : t.group) (e : g⁻¹ * k = h) :
    C.comp (convolutionHom C hC t f q k)
      (convolutionComponentReindexData C hC t X' Y' k g h e).hom =
      C.smul ((-1 : ℝ) ^ (t.nu g h * (a + b)).val)
        (C.comp (convolutionComponentReindexData C hC t X Y k g h e).hom
          (C.tensorHom (f g) (q h))) := by
  have hn := indexed_morphism_eq_naturality
    ⟨C.toWeaklyPointedSuperfusionData, hC.toWeaklyPointedSuperfusionLaws⟩
    (fun l => C.tensorObj (X g).val (Y l).val)
    (fun l => C.tensorObj (X' g).val (Y' l).val)
    (fun l => C.tensorHom (f g) (q l)) e
    (congrArg (fun l => C.tensorObj (X g).val (Y l).val) e)
    (congrArg (fun l => C.tensorObj (X' g).val (Y' l).val) e)
  dsimp only [convolutionComponentReindexData, IsoData.trans]
  rw [← hC.comp_assoc, convolutionComponentComparison_naturality C hC t f q hf hq,
    hC.smul_comp, hC.comp_assoc, hn, ← hC.comp_assoc]
  rw [show t.nu g (g⁻¹ * k) = t.nu g h from congrArg (t.nu g) e]

end RMod.Classification
