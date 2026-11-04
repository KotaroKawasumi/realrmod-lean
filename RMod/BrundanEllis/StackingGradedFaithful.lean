import RMod.BrundanEllis.StackingFunctorPi
import RMod.BrundanEllis.StackingFaithfulForget

/-! Full faithfulness on homogeneous Hom spaces implies full faithfulness
on total morphisms and reflection of homogeneous isomorphisms. These
facts apply before a fusion or monoidal structure has been assembled. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace RMod.BrundanEllis.Stacking
variable {C D : Type} [SuperCategory C] [SuperCategory D]
  (F : SuperFunctor C D) (hF : ∀ X Y a, Function.Bijective (F.map X Y a))

def totalFullyFaithful : (totalSuperFunctor F).FullyFaithful where
  preimage {X Y} f a := (superHomIso F hF X Y).inv a (f a)
  map_preimage {X Y} f := by
    funext a
    exact congrArg (fun k => k a (f a)) (superHomIso F hF X Y).inv_hom_id
  preimage_map {X Y} f := by
    funext a
    exact congrArg (fun k => k a (f a)) (superHomIso F hF X Y).hom_inv_id

include hF in
 theorem map_grade_iff {X Y : C} {a : ZMod 2} (f : THom C X Y) :
    tMap F f ∈ grade D (F.obj X) (F.obj Y) a ↔ f ∈ grade C X Y a := by
  constructor
  · intro h b hb
    apply (hF X Y b).injective
    change F.map X Y b (f b) = F.map X Y b 0
    exact (h b hb).trans (map_zero _).symm
  · intro h b hb
    change F.map X Y b (f b) = 0
    rw [h b hb, map_zero]

include hF in
 theorem reflect_parity_orbit {X Y : C}
    (h : SameParityOrbit D (F.obj X) (F.obj Y)) : SameParityOrbit C X Y := by
  obtain ⟨a, e, hf, hg⟩ := h
  let T := totalSuperFunctor F
  let ff := totalFullyFaithful F hF
  letI : T.Full := ff.full
  letI : T.Faithful := ff.faithful
  let u := T.preimageIso e
  refine ⟨a, u, ?_, ?_⟩
  · apply (map_grade_iff F hF u.hom).mp
    have hm : tMap F u.hom = e.hom := T.map_preimage e.hom
    exact hm.symm ▸ hf
  · apply (map_grade_iff F hF u.inv).mp
    have hm : tMap F u.inv = e.inv := T.map_preimage e.inv
    exact hm.symm ▸ hg

end RMod.BrundanEllis.Stacking
