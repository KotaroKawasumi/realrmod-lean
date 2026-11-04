import RMod.Classification.Proofs.RightParityComparison

/-!
# Naturality of the even central comparison on all morphisms

Postcomposing the central comparison with the right odd comparison
recovers the left odd comparison. Their identical supernatural signs
therefore cancel. Decomposing an arbitrary morphism into its two grades
extends the resulting even naturality equation to the full Hom space.
-/

set_option autoImplicit false
universe u v

namespace RMod.Classification.PiLaws

variable {C : WeaklyPointedSuperfusionData.{u, v}}
  (hC : WeaklyPointedSuperfusionLaws C) {p : PiData C} (hp : PiLaws C p)

include hC hp

theorem central_rightZ (X : C.Obj) :
    C.comp (p.centralHom X) (p.rightZHom X) = p.zHom X := by
  change C.comp (C.comp (p.zHom X) (p.rightZInv X)) (p.rightZHom X) = p.zHom X
  rw [hC.comp_assoc, (hp.rightZ_iso hC X).inv_hom, hC.comp_id]

theorem central_naturality_homogeneous {X Y : C.Obj} {a : ZMod 2} (f : C.Hom X Y)
    (hf : C.IsHomogeneous a f) :
    C.comp (C.tensorHom (C.id p.object) f) (p.centralHom Y) =
      C.comp (p.centralHom X) (C.tensorHom f (C.id p.object)) := by
  have h :
      C.comp (C.comp (C.tensorHom (C.id p.object) f) (p.centralHom Y)) (p.rightZHom Y) =
        C.comp (C.comp (p.centralHom X) (C.tensorHom f (C.id p.object))) (p.rightZHom Y) := by
    rw [hC.comp_assoc, hp.central_rightZ hC Y, hC.comp_assoc,
      hp.rightZ_naturality hC f hf, hC.comp_smul, ← hC.comp_assoc,
      hp.central_rightZ hC X]
    exact hp.z_naturality hC f hf
  have h' := congrArg (fun k => C.comp k (p.rightZInv Y)) h
  simpa only [hC.comp_assoc, (hp.rightZ_iso hC Y).hom_inv, hC.comp_id] using h'

theorem central_naturality {X Y : C.Obj} (f : C.Hom X Y) :
    C.comp (C.tensorHom (C.id p.object) f) (p.centralHom Y) =
      C.comp (p.centralHom X) (C.tensorHom f (C.id p.object)) := by
  obtain ⟨f₀, f₁, h₀, h₁, he⟩ := hC.grade_decomposition f
  rw [← he]
  simp only [hC.tensor_add_left, hC.tensor_add_right, hC.add_comp, hC.comp_add,
    hp.central_naturality_homogeneous hC f₀ h₀,
    hp.central_naturality_homogeneous hC f₁ h₁]

theorem central_inv_naturality {X Y : C.Obj} (f : C.Hom X Y) :
    C.comp (C.tensorHom f (C.id p.object)) (p.centralInv Y) =
      C.comp (p.centralInv X) (C.tensorHom (C.id p.object) f) := by
  calc
    _ = C.comp (C.comp (p.centralInv X) (p.centralHom X))
        (C.comp (C.tensorHom f (C.id p.object)) (p.centralInv Y)) := by
      rw [(hp.central_iso hC X).inv_hom, hC.id_comp]
    _ = C.comp (p.centralInv X)
        (C.comp (C.comp (p.centralHom X) (C.tensorHom f (C.id p.object))) (p.centralInv Y)) := by
      simp only [hC.comp_assoc]
    _ = _ := by
      rw [← hp.central_naturality hC f, hC.comp_assoc,
        (hp.central_iso hC Y).hom_inv, hC.comp_id]

end RMod.Classification.PiLaws
