import RMod.Classification.Proofs.RetractSumTransport

/-!
# The completed transported homogeneous sum

The copied parities and explicit transported matrix units are bundled
with their proved degree, diagonal, off-diagonal and total identities.
-/

set_option autoImplicit false

namespace RMod.Classification

open CategoryTheory

def retractSumTransport {C D : WeaklyPointedSuperfusion.{0, 0}}
    {X : LinearCategory C} {Y : LinearCategory D}
    (d : SimpleRetract C X) (t : SimpleRetract D Y) (φ : End X ≃ₐ[ℝ] End Y)
    {n : ℕ} (A : HomogeneousSum C.data d.data.object X n)
    (hproj : SimpleRetract.projectorData t.data = φ (SimpleRetract.projectorData d.data))
    (hφ : ∀ {a : ZMod 2} {f : End X}, C.data.IsHomogeneous a f → D.data.IsHomogeneous a (φ f)) :
    HomogeneousSum D.data t.data.object Y n :=
  ⟨retractSumTransportData C D d.data t.data φ A.data, retractSumTransportLaws d t φ A hproj hφ⟩

end RMod.Classification
