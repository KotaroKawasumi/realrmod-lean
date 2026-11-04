import RMod.BrundanEllis.StackingSuperInterchangeAssociativity
import RMod.BrundanEllis.StackingInterchangeUnit

/-! Unit coherence for the super shuffle follows by lifting even unit crossings to the parity cover. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u v
namespace RMod.BrundanEllis.Stacking
open RMod.Classification CategoryTheory CategoryTheory.MonoidalCategory
variable (S : WeaklyPointedSuperfusion.{u, v})

/-- The left unit comparison of a homogeneous shuffle, at degree zero. -/
theorem superInterchange_leftUnit (X Y : S.data.Obj)
    (e : S.data.Hom (S.data.tensorObj S.data.tensorUnit X) (S.data.tensorObj X S.data.tensorUnit))
    (he0 : S.data.IsHomogeneous 0 e)
    (he : S.data.comp e (S.data.rightUnitorHom X) = S.data.leftUnitorHom X) :
    S.data.comp (superInterchangeHom S S.data.tensorUnit S.data.tensorUnit X Y e)
      (S.data.tensorHom (S.data.leftUnitorHom X) (S.data.leftUnitorHom Y)) =
    S.data.comp
      (S.data.tensorHom (S.data.leftUnitorHom S.data.tensorUnit) (S.data.id (S.data.tensorObj X Y)))
      (S.data.leftUnitorHom (S.data.tensorObj X Y)) := by
  let X₀ : ParityCover S := (X, 0)
  let Y₀ : ParityCover S := (Y, 0)
  let e' : (𝟙_ (ParityCover S)) ⊗ X₀ ⟶ X₀ ⊗ (𝟙_ (ParityCover S)) :=
    ⟨e, by simpa [X₀] using he0⟩
  have he' : e' ≫ (ρ_ X₀).hom = (λ_ X₀).hom := Subtype.ext he
  have hh := congrArg (fun f => f.val) (interchangeMap_leftUnit X₀ Y₀ e' he')
  simpa only [interchangeMap, superInterchangeHom, ← id_tensorHom, ← tensorHom_id,
    ParityCover.comp_val, ParityCover.tensor_val, ParityCover.id_val,
    ParityCover.assoc_hom_val, ParityCover.assoc_inv_val,
    ParityCover.leftUnit_hom_val, ParityCover.rightUnit_hom_val,
    ParityCover.tensorObj_snd, ParityCover.tensorObj_fst,
    ParityCover.unit_snd, ParityCover.unit_fst, X₀, Y₀, e',
    add_zero, zero_mul, ZMod.val_zero, pow_zero, S.laws.one_smul] using hh

/-- The right unit comparison of the same homogeneous shuffle. -/
theorem superInterchange_rightUnit (X Y : S.data.Obj)
    (e : S.data.Hom (S.data.tensorObj Y S.data.tensorUnit) (S.data.tensorObj S.data.tensorUnit Y))
    (he0 : S.data.IsHomogeneous 0 e)
    (he : S.data.comp e (S.data.leftUnitorHom Y) = S.data.rightUnitorHom Y) :
    S.data.comp (superInterchangeHom S X Y S.data.tensorUnit S.data.tensorUnit e)
      (S.data.tensorHom (S.data.rightUnitorHom X) (S.data.rightUnitorHom Y)) =
    S.data.comp
      (S.data.tensorHom (S.data.id (S.data.tensorObj X Y)) (S.data.leftUnitorHom S.data.tensorUnit))
      (S.data.rightUnitorHom (S.data.tensorObj X Y)) := by
  let X₀ : ParityCover S := (X, 0)
  let Y₀ : ParityCover S := (Y, 0)
  let e' : Y₀ ⊗ (𝟙_ (ParityCover S)) ⟶ (𝟙_ (ParityCover S)) ⊗ Y₀ :=
    ⟨e, by simpa [Y₀] using he0⟩
  have he' : e' ≫ (λ_ Y₀).hom = (ρ_ Y₀).hom := Subtype.ext he
  have hh := congrArg (fun f => f.val) (interchangeMap_rightUnit X₀ Y₀ e' he')
  simpa only [interchangeMap, superInterchangeHom, ← id_tensorHom, ← tensorHom_id,
    ParityCover.comp_val, ParityCover.tensor_val, ParityCover.id_val,
    ParityCover.assoc_hom_val, ParityCover.assoc_inv_val,
    ParityCover.leftUnit_hom_val, ParityCover.rightUnit_hom_val,
    ParityCover.tensorObj_snd, ParityCover.tensorObj_fst,
    ParityCover.unit_snd, ParityCover.unit_fst, X₀, Y₀, e',
    add_zero, zero_mul, ZMod.val_zero, pow_zero, S.laws.one_smul] using hh

end RMod.BrundanEllis.Stacking
