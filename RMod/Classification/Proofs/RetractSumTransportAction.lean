import RMod.Classification.Instances.RetractSumTransport
import RMod.Classification.Instances.SimpleCornerEquivalence
import RMod.Classification.Instances.HomogeneousHomMatrix
import RMod.Classification.Instances.HomogeneousHomTransport

/-!
# The transported presentation reproduces the given algebra action

Every matrix coefficient of the given ambient image is the corner image
of the original coefficient. Consequently matrix transport through the
induced simple-corner equivalence is exactly the original algebra map
on all ambient endomorphisms, not merely an abstract isomorphism of
the two algebras.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

attribute [local implicit_reducible] CategoryTheory.End Matrix

variable {C D : WeaklyPointedSuperfusion.{0, 0}} {X : LinearCategory C} {Y : LinearCategory D}
  (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
  {n : ℕ} (A : HomogeneousSum C.data d.data.object X n)

theorem retractSumTransport_action_coefficient (f : End X) (i j : Fin n) :
    D.data.comp (retractSumTransportData C D d.data t.data φ A.data |>.inclusion i)
      (D.data.comp (φ f) (retractSumTransportData C D d.data t.data φ A.data |>.projection j)) =
    simpleCornerMap C D d.data t.data φ
      (C.data.comp (A.data.inclusion i) (C.data.comp f (A.data.projection j))) := by
  change D.data.comp
    (D.data.comp t.data.inclusion (φ (C.data.comp d.data.projection (A.data.inclusion i))))
    (D.data.comp (φ f) (D.data.comp (φ (C.data.comp (A.data.projection j) d.data.inclusion))
      t.data.projection)) =
    D.data.comp t.data.inclusion (D.data.comp
      (φ (C.data.comp d.data.projection (C.data.comp
        (C.data.comp (A.data.inclusion i) (C.data.comp f (A.data.projection j))) d.data.inclusion)))
      t.data.projection)
  rw [D.laws.comp_assoc, ← D.laws.comp_assoc (φ f), ← endAlgEquiv_map_comp C D φ,
    ← D.laws.comp_assoc (φ (C.data.comp d.data.projection (A.data.inclusion i))),
    ← endAlgEquiv_map_comp C D φ]
  simp only [C.laws.comp_assoc]

variable (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))
  (hφ : ∀ {a : ZMod 2} {f : End X}, C.data.IsHomogeneous a f → D.data.IsHomogeneous a (φ f))

theorem retractSumTransport_action_matrix (f : End X) :
    let B := retractSumTransport d t φ A hproj hφ
    HomogeneousSum.toHomMatrix B B (φ f) =
      (HomogeneousSum.toHomMatrix A A f).map (simpleCornerEquivalence d t φ hproj) := by
  ext i j
  exact retractSumTransport_action_coefficient d t φ A f j i

theorem retractSumTransport_action (f : End X) :
    let B := retractSumTransport d t φ A hproj hφ
    HomogeneousSum.transportHom (simpleCornerEquivalence d t φ hproj) A A B B f = φ f := by
  let B := retractSumTransport d t φ A hproj hφ
  apply (HomogeneousSum.homMatrixLinearEquiv B B).injective
  exact (HomogeneousSum.toHomMatrix_transportHom (simpleCornerEquivalence d t φ hproj)
    A A B B f).trans (retractSumTransport_action_matrix d t φ A hproj hφ f).symm

end RMod.Classification
