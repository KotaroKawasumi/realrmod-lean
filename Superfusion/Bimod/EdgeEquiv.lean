/-
Superfusion / Bimod / EdgeEquiv

Milestone M8a-8c′-2b-ii (roadmap v3, first block): **equivariance of
the pentagon edges** — with all five vertices carrying their slot
actions (2a″–2b-i‴), each edge transports them; the composites of
the two routes are then intertwiners of the endpoint structures.

This block: **the first edge** `E1 t = t ⊗ id : Q1 → Q2`.  All six
transports are direct vertex-level instantiations of the
`RelTensor.map` lemmas of M8a-8b′-1, `congrArg`-descended to the
`compHom` scalar actions:

* the `a`, `b`, `c`-slots (through the route factor): `t`'s own slot
  (super-)equivariance passes through with its scalar;
* the `d`-slot (the signed middle action through the column): the
  sign `(-1)^{e|t_d|}` produced by `t`'s degree shift of the
  first-factor parity;
* the right action: plain;
* the grading: degree `e`.
-/
import Superfusion.Bimod.QuadActions

namespace Superfusion

namespace Bimod

namespace PentagonB

open scoped TensorProduct

variable (K : Type*) [Field K] [Invertible (2 : K)]
variable (a b c d : ZMod 8)

namespace E1

variable (t : BL K a b c →ₗ[K] BR K a b c)
variable (ht : ∀ (τ : (stdTower (K := K) (a + b + c)).carrier)
  (m : BL K a b c),
  t (MulOpposite.op τ • m) = MulOpposite.op τ • t m)

/-- `E1` transports a slot action through the route factor, with
`t`'s own equivariance scalar (`a`, `b`, `c`-slots alike). -/
theorem comp_aslot {s : ℤ} {x : (stdTower (K := K) a).carrier}
    (htA : ∀ m : BL K a b c, t (x • m) = s • (x • t m))
    (z : Q1 K a b c d) :
    E1 K a b c d t ht (x • z) = s • (x • E1 K a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_leftActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (B := (stdTower (K := K) a).carrier) htA)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

theorem comp_bslot {s : ℤ} {y : (stdTower (K := K) b).carrier}
    (htB : ∀ m : BL K a b c, t (y • m) = s • (y • t m))
    (z : Q1 K a b c d) :
    E1 K a b c d t ht (y • z) = s • (y • E1 K a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_leftActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (B := (stdTower (K := K) b).carrier) htB)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

theorem comp_cslot {s : ℤ} {z₀ : (stdTower (K := K) c).carrier}
    (htC : ∀ m : BL K a b c, t (z₀ • m) = s • (z₀ • t m))
    (z : Q1 K a b c d) :
    E1 K a b c d t ht (z₀ • z) = s • (z₀ • E1 K a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_leftActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (B := (stdTower (K := K) c).carrier) htC)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

/-- `E1` transports the `d`-slot middle action up to the sign
`(-1)^{e|τ|}` of `t`'s degree shift. -/
theorem comp_dslot {e : ZMod 2}
    (hte : ∀ j : ZMod 2, ∀ m ∈ BL.grading K a b c j,
      t m ∈ BR.grading K a b c (j + e))
    {k : ZMod 2} {τ : (stdTower (K := K) d).carrier}
    (hτ : τ ∈ (stdTower (K := K) d).grading k) (z : Q1 K a b c d) :
    E1 K a b c d t ht (τ • z)
      = ((sgn (e * k) : ℤˣ) : ℤ) • (τ • E1 K a b c d t ht z) := by
  have h' := congrArg (fun F => F z)
    (map_comp_midEnd t LinearMap.id
      (stdTower (K := K) (a + b + c)).grading (BL.grading K a b c)
      (BR.grading K a b c) (stdTower (K := K) d).grading
      (TowerColumn.superCommSMul K (a + b + c) d)
      (TowerColumn.superCommSMul K (a + b + c) d)
      ht (fun _ _ => rfl) hte hτ (fun _ => rfl))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h'
  exact h'

/-- `E1` transports the right action plainly. -/
theorem comp_right
    (τ : ((stdTower (K := K) (a + b + c + d)).carrier)ᵐᵒᵖ)
    (z : Q1 K a b c d) :
    E1 K a b c d t ht (τ • z) = τ • E1 K a b c d t ht z := by
  have h' := congrArg (fun F => F z)
    (map_comp_rightActionEnd t LinearMap.id ht (fun _ _ => rfl)
      (e := τ) (fun _ => rfl))
  simp only [LinearMap.comp_apply] at h'
  exact h'

/-- `E1` is homogeneous of `t`'s degree. -/
theorem mem_grading {e : ZMod 2}
    (hte : ∀ j : ZMod 2, ∀ m ∈ BL.grading K a b c j,
      t m ∈ BR.grading K a b c (j + e))
    {i : ZMod 2} {z : Q1 K a b c d} (hz : z ∈ Q1.grading K a b c d i) :
    E1 K a b c d t ht z ∈ Q2.grading K a b c d (i + e) := by
  have h := map_mem_relGrading_of_degree t LinearMap.id
    (BL.grading K a b c) (TowerColumn.grading K (a + b + c) d)
    (BR.grading K a b c) (TowerColumn.grading K (a + b + c) d)
    ht (fun _ _ => rfl) hte
    (fun j v hv => by rwa [add_zero] : ∀ j : ZMod 2,
      ∀ v ∈ TowerColumn.grading K (a + b + c) d j,
        LinearMap.id v ∈ TowerColumn.grading K (a + b + c) d (j + 0))
    hz
  rwa [show e + (0 : ZMod 2) = 0 + e from by rw [add_zero, zero_add],
    ← add_assoc, add_zero] at h
end E1

end PentagonB

end Bimod

end Superfusion
