import Superfusion.RMod.RawDCT.C

/-!
# Abstract actual ternary routes and raw connectors

This file contains only the abstract `D → C → T` layer.  A ternary route
stores its actual carrier and every executable operation.  `TData` stores two
such route-data records, their finite coordinate presentations, and the
explicit connector maps.  All assertions about those exact records occur in
`TripleRouteLaws` and `TLaws`; the completed structures merely bundle data
with their dependent laws.
-/

set_option autoImplicit false

namespace Superfusion.RMod.RawDCT

/-! ## Actual triple-route data -/

/-- Computational contents of an actual ternary graded bimodule. -/
structure TripleRouteData (dD : DData) where
  carrier : ZMod 8 → ZMod 8 → ZMod 8 → Type
  zero : ∀ a b c, carrier a b c
  add : ∀ a b c, carrier a b c → carrier a b c → carrier a b c
  neg : ∀ a b c, carrier a b c → carrier a b c
  smul : ∀ a b c, ℝ → carrier a b c → carrier a b c
  component : ∀ a b c, ZMod 2 → carrier a b c → carrier a b c
  leftPure : ∀ a b c,
    (dD.algebra a).carrier → (dD.algebra b).carrier →
      (dD.algebra c).carrier → carrier a b c → carrier a b c
  right : ∀ a b c,
    carrier a b c → (dD.algebra (a + b + c)).carrier → carrier a b c

namespace TripleRouteData

/-- Homogeneity derived from the stored executable route projection. -/
def MemGrade {dD : DData} (dR : TripleRouteData dD)
    (a b c : ZMod 8) (i : ZMod 2) (x : dR.carrier a b c) : Prop :=
  dR.component a b c i x = x

end TripleRouteData

/-- All additive, scalar, grading, and bimodule laws of one exact route-data
record. -/
structure TripleRouteLaws (dD : DData) (hD : DLaws dD)
    (dR : TripleRouteData dD) : Prop where
  add_assoc : ∀ a b c (x y z : dR.carrier a b c),
    dR.add a b c (dR.add a b c x y) z =
      dR.add a b c x (dR.add a b c y z)
  add_comm : ∀ a b c (x y : dR.carrier a b c),
    dR.add a b c x y = dR.add a b c y x
  zero_add : ∀ a b c (x : dR.carrier a b c),
    dR.add a b c (dR.zero a b c) x = x
  add_zero : ∀ a b c (x : dR.carrier a b c),
    dR.add a b c x (dR.zero a b c) = x
  neg_add : ∀ a b c (x : dR.carrier a b c),
    dR.add a b c (dR.neg a b c x) x = dR.zero a b c
  add_neg : ∀ a b c (x : dR.carrier a b c),
    dR.add a b c x (dR.neg a b c x) = dR.zero a b c

  one_smul : ∀ a b c (x : dR.carrier a b c), dR.smul a b c 1 x = x
  smul_assoc : ∀ a b c r s (x : dR.carrier a b c),
    dR.smul a b c (r * s) x = dR.smul a b c r (dR.smul a b c s x)
  add_smul : ∀ a b c r s (x : dR.carrier a b c),
    dR.smul a b c (r + s) x =
      dR.add a b c (dR.smul a b c r x) (dR.smul a b c s x)
  smul_add : ∀ a b c r (x y : dR.carrier a b c),
    dR.smul a b c r (dR.add a b c x y) =
      dR.add a b c (dR.smul a b c r x) (dR.smul a b c r y)
  zero_smul : ∀ a b c (x : dR.carrier a b c),
    dR.smul a b c 0 x = dR.zero a b c
  smul_zero : ∀ a b c r, dR.smul a b c r (dR.zero a b c) = dR.zero a b c

  component_zero : ∀ a b c i,
    dR.component a b c i (dR.zero a b c) = dR.zero a b c
  component_add : ∀ a b c i (x y : dR.carrier a b c),
    dR.component a b c i (dR.add a b c x y) =
      dR.add a b c (dR.component a b c i x) (dR.component a b c i y)
  component_neg : ∀ a b c i (x : dR.carrier a b c),
    dR.component a b c i (dR.neg a b c x) =
      dR.neg a b c (dR.component a b c i x)
  component_smul : ∀ a b c i r (x : dR.carrier a b c),
    dR.component a b c i (dR.smul a b c r x) =
      dR.smul a b c r (dR.component a b c i x)
  component_idem : ∀ a b c i (x : dR.carrier a b c),
    dR.component a b c i (dR.component a b c i x) = dR.component a b c i x
  component_complement : ∀ a b c i (x : dR.carrier a b c),
    dR.add a b c (dR.component a b c i x)
      (dR.component a b c (i + 1) x) = x
  grade_disjoint : ∀ a b c i (x : dR.carrier a b c),
    dR.MemGrade a b c i x → dR.MemGrade a b c (i + 1) x →
      x = dR.zero a b c

  left_zero_first : ∀ a b c (y : (dD.algebra b).carrier)
      (z : (dD.algebra c).carrier) (m : dR.carrier a b c),
    dR.leftPure a b c (dD.algebra a).zero y z m = dR.zero a b c
  left_zero_second : ∀ a b c (x : (dD.algebra a).carrier)
      (z : (dD.algebra c).carrier) (m : dR.carrier a b c),
    dR.leftPure a b c x (dD.algebra b).zero z m = dR.zero a b c
  left_zero_third : ∀ a b c (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (m : dR.carrier a b c),
    dR.leftPure a b c x y (dD.algebra c).zero m = dR.zero a b c
  left_zero_module : ∀ a b c (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier),
    dR.leftPure a b c x y z (dR.zero a b c) = dR.zero a b c
  left_add_first : ∀ a b c (x x' : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c ((dD.algebra a).add x x') y z m =
      dR.add a b c (dR.leftPure a b c x y z m)
        (dR.leftPure a b c x' y z m)
  left_add_second : ∀ a b c (x : (dD.algebra a).carrier)
      (y y' : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c x ((dD.algebra b).add y y') z m =
      dR.add a b c (dR.leftPure a b c x y z m)
        (dR.leftPure a b c x y' z m)
  left_add_third : ∀ a b c (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z z' : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c x y ((dD.algebra c).add z z') m =
      dR.add a b c (dR.leftPure a b c x y z m)
        (dR.leftPure a b c x y z' m)
  left_add_module : ∀ a b c (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m n : dR.carrier a b c),
    dR.leftPure a b c x y z (dR.add a b c m n) =
      dR.add a b c (dR.leftPure a b c x y z m)
        (dR.leftPure a b c x y z n)
  left_smul_first : ∀ a b c r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c ((dD.algebra a).smul r x) y z m =
      dR.smul a b c r (dR.leftPure a b c x y z m)
  left_smul_second : ∀ a b c r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c x ((dD.algebra b).smul r y) z m =
      dR.smul a b c r (dR.leftPure a b c x y z m)
  left_smul_third : ∀ a b c r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c x y ((dD.algebra c).smul r z) m =
      dR.smul a b c r (dR.leftPure a b c x y z m)
  left_smul_module : ∀ a b c r (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c),
    dR.leftPure a b c x y z (dR.smul a b c r m) =
      dR.smul a b c r (dR.leftPure a b c x y z m)
  left_one : ∀ a b c (m : dR.carrier a b c),
    dR.leftPure a b c (dD.algebra a).one (dD.algebra b).one
      (dD.algebra c).one m = m
  left_mul : ∀ a b c i' j k j'
      (x x' : (dD.algebra a).carrier)
      (y y' : (dD.algebra b).carrier)
      (z z' : (dD.algebra c).carrier) (m : dR.carrier a b c),
    (dD.algebra b).MemGrade j y →
    (dD.algebra c).MemGrade k z →
    (dD.algebra a).MemGrade i' x' →
    (dD.algebra b).MemGrade j' y' →
    dR.leftPure a b c x y z (dR.leftPure a b c x' y' z' m) =
      dR.smul a b c (paritySign (j * i' + k * (i' + j')))
        (dR.leftPure a b c ((dD.algebra a).mul x x')
          ((dD.algebra b).mul y y') ((dD.algebra c).mul z z') m)
  left_memGrade : ∀ a b c i j k l
      (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
      (z : (dD.algebra c).carrier) (m : dR.carrier a b c),
    (dD.algebra a).MemGrade i x →
    (dD.algebra b).MemGrade j y →
    (dD.algebra c).MemGrade k z →
    dR.MemGrade a b c l m →
    dR.MemGrade a b c (i + j + k + l) (dR.leftPure a b c x y z m)

  right_zero_module : ∀ a b c (x : (dD.algebra (a + b + c)).carrier),
    dR.right a b c (dR.zero a b c) x = dR.zero a b c
  right_zero_algebra : ∀ a b c (m : dR.carrier a b c),
    dR.right a b c m (dD.algebra (a + b + c)).zero = dR.zero a b c
  right_add_module : ∀ a b c (m n : dR.carrier a b c)
      (x : (dD.algebra (a + b + c)).carrier),
    dR.right a b c (dR.add a b c m n) x =
      dR.add a b c (dR.right a b c m x) (dR.right a b c n x)
  right_add_algebra : ∀ a b c (m : dR.carrier a b c)
      (x y : (dD.algebra (a + b + c)).carrier),
    dR.right a b c m ((dD.algebra (a + b + c)).add x y) =
      dR.add a b c (dR.right a b c m x) (dR.right a b c m y)
  right_smul_module : ∀ a b c r (m : dR.carrier a b c)
      (x : (dD.algebra (a + b + c)).carrier),
    dR.right a b c (dR.smul a b c r m) x =
      dR.smul a b c r (dR.right a b c m x)
  right_smul_algebra : ∀ a b c r (m : dR.carrier a b c)
      (x : (dD.algebra (a + b + c)).carrier),
    dR.right a b c m ((dD.algebra (a + b + c)).smul r x) =
      dR.smul a b c r (dR.right a b c m x)
  right_one : ∀ a b c (m : dR.carrier a b c),
    dR.right a b c m (dD.algebra (a + b + c)).one = m
  right_assoc : ∀ a b c (m : dR.carrier a b c)
      (x y : (dD.algebra (a + b + c)).carrier),
    dR.right a b c (dR.right a b c m x) y =
      dR.right a b c m ((dD.algebra (a + b + c)).mul x y)
  right_memGrade : ∀ a b c i j (m : dR.carrier a b c)
      (x : (dD.algebra (a + b + c)).carrier),
    dR.MemGrade a b c i m →
    (dD.algebra (a + b + c)).MemGrade j x →
    dR.MemGrade a b c (i + j) (dR.right a b c m x)
  actions_comm : ∀ a b c (x : (dD.algebra a).carrier)
      (y : (dD.algebra b).carrier) (z : (dD.algebra c).carrier)
      (m : dR.carrier a b c) (q : (dD.algebra (a + b + c)).carrier),
    dR.right a b c (dR.leftPure a b c x y z m) q =
      dR.leftPure a b c x y z (dR.right a b c m q)

/-- A completed actual ternary route over a completed coefficient family. -/
structure TripleRoute (D : D) where
  data : TripleRouteData D.data
  laws : TripleRouteLaws D.data D.laws data

/-! ## Coordinate presentations and connector data -/

/-- Finite coordinates of the left-associated route. -/
abbrev LeftRouteCoordinates {dD : DData} (dC : CData dD)
    (a b c : ZMod 8) : Type :=
  dC.Index a b → dC.Index (a + b) c →
    (dD.algebra (a + b + c)).carrier

/-- Finite coordinates of the right-associated route. -/
abbrev RightRouteCoordinates {dD : DData} (dC : CData dD)
    (a b c : ZMod 8) : Type :=
  dC.Index b c → dC.Index a (b + c) →
    (dD.algebra (a + b + c)).carrier

/-- Computational contents of a raw ternary connector. -/
structure TData (dD : DData) (dC : CData dD) where
  leftRoute : TripleRouteData dD
  rightRoute : TripleRouteData dD
  leftToCoord : ∀ a b c, leftRoute.carrier a b c →
    LeftRouteCoordinates dC a b c
  leftOfCoord : ∀ a b c, LeftRouteCoordinates dC a b c →
    leftRoute.carrier a b c
  rightToCoord : ∀ a b c, rightRoute.carrier a b c →
    RightRouteCoordinates dC a b c
  rightOfCoord : ∀ a b c, RightRouteCoordinates dC a b c →
    rightRoute.carrier a b c
  parity : ZMod 8 → ZMod 8 → ZMod 8 → ZMod 2
  hom : ∀ a b c, leftRoute.carrier a b c → rightRoute.carrier a b c
  inv : ∀ a b c, rightRoute.carrier a b c → leftRoute.carrier a b c

namespace TData

abbrev LeftCarrier {dD : DData} {dC : CData dD} (dT : TData dD dC)
    (a b c : ZMod 8) : Type := dT.leftRoute.carrier a b c

abbrev RightCarrier {dD : DData} {dC : CData dD} (dT : TData dD dC)
    (a b c : ZMod 8) : Type := dT.rightRoute.carrier a b c

end TData

/-! ## Coordinate formulas determined by `CData` -/

/-- Twist the odd part of a coefficient by the parity of an outer route row.

For a homogeneous input of degree `j` this is multiplication by
`paritySign (p * j)`.  Keeping the projection explicit makes the operation
computable for an arbitrary, not necessarily homogeneous, input. -/
def routeRowTwist (dD : DData) (a : ZMod 8) (p : ZMod 2)
    (x : (dD.algebra a).carrier) : (dD.algebra a).carrier :=
  (dD.algebra a).add ((dD.algebra a).component 0 x)
    ((dD.algebra a).smul (paritySign p) ((dD.algebra a).component 1 x))

/-- One matrix coefficient of the left-associated pure action.

The second fusion stage carries the middle-action Koszul sign.  In the
even-first route frame this is the parity twist of the `c` input by the
outer source-row parity. -/
def leftRouteCoeff {dD : DData} (dC : CData dD) (a b c : ZMod 8)
    (targetAB : dC.Index a b) (targetABC : dC.Index (a + b) c)
    (sourceAB : dC.Index a b) (sourceABC : dC.Index (a + b) c)
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) :
    (dD.algebra (a + b + c)).carrier :=
  dC.leftCoeff (a + b) c targetABC sourceABC
    (dC.leftCoeff a b targetAB sourceAB x y)
    (routeRowTwist dD c (dC.rowParity a b sourceAB) z)

/-- Computational transport along associativity of the endpoint label. -/
def routeCastAssoc (dD : DData) (a b c : ZMod 8) :
    (dD.algebra (a + (b + c))).carrier →
      (dD.algebra (a + b + c)).carrier :=
  cast (congrArg (fun t : ZMod 8 => (dD.algebra t).carrier)
    (_root_.add_assoc a b c).symm)

/-- One matrix coefficient of the right-associated pure action.

Here the middle-action Koszul sign twists the `a` input by the outer target
row of the `(b,c)` kernel.  There is no global twist of `y` or `z`:
associativity of the graded tensor product is signless on pure tensors. -/
def rightRouteCoeff {dD : DData} (dC : CData dD) (a b c : ZMod 8)
    (targetBC : dC.Index b c) (targetABC : dC.Index a (b + c))
    (sourceBC : dC.Index b c) (sourceABC : dC.Index a (b + c))
    (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
    (z : (dD.algebra c).carrier) :
    (dD.algebra (a + b + c)).carrier :=
  routeCastAssoc dD a b c <|
    dC.leftCoeff a (b + c) targetABC sourceABC
      (routeRowTwist dD a (dC.rowParity b c targetBC) x)
      (dC.leftCoeff b c targetBC sourceBC y z)

/-! ## Laws of the exact stored connector data -/

/-- Route presentations, module laws, connector linearity, graded
equivariance, homogeneity, and two-sided inverse laws for one `TData`. -/
structure TLaws (dD : DData) (hD : DLaws dD)
    (dC : CData dD) (hC : CLaws dD hD dC) (dT : TData dD dC) : Prop where
  left_route_laws : TripleRouteLaws dD hD dT.leftRoute
  right_route_laws : TripleRouteLaws dD hD dT.rightRoute

  left_ofCoord_toCoord : ∀ a b c (x : dT.LeftCarrier a b c),
    dT.leftOfCoord a b c (dT.leftToCoord a b c x) = x
  left_toCoord_ofCoord : ∀ a b c (x : LeftRouteCoordinates dC a b c),
    dT.leftToCoord a b c (dT.leftOfCoord a b c x) = x
  right_ofCoord_toCoord : ∀ a b c (x : dT.RightCarrier a b c),
    dT.rightOfCoord a b c (dT.rightToCoord a b c x) = x
  right_toCoord_ofCoord : ∀ a b c (x : RightRouteCoordinates dC a b c),
    dT.rightToCoord a b c (dT.rightOfCoord a b c x) = x

  left_toCoord_zero : ∀ a b c,
    dT.leftToCoord a b c (dT.leftRoute.zero a b c) =
      fun _ _ => (dD.algebra (a + b + c)).zero
  left_toCoord_add : ∀ a b c (x y : dT.LeftCarrier a b c),
    dT.leftToCoord a b c (dT.leftRoute.add a b c x y) = fun r s =>
      (dD.algebra (a + b + c)).add
        (dT.leftToCoord a b c x r s) (dT.leftToCoord a b c y r s)
  left_toCoord_neg : ∀ a b c (x : dT.LeftCarrier a b c),
    dT.leftToCoord a b c (dT.leftRoute.neg a b c x) = fun r s =>
      (dD.algebra (a + b + c)).neg (dT.leftToCoord a b c x r s)
  left_toCoord_smul : ∀ a b c q (x : dT.LeftCarrier a b c),
    dT.leftToCoord a b c (dT.leftRoute.smul a b c q x) = fun r s =>
      (dD.algebra (a + b + c)).smul q (dT.leftToCoord a b c x r s)
  left_toCoord_component : ∀ a b c i (x : dT.LeftCarrier a b c),
    dT.leftToCoord a b c (dT.leftRoute.component a b c i x) = fun r s =>
      (dD.algebra (a + b + c)).component
        (i + dC.rowParity a b r + dC.rowParity (a + b) c s)
        (dT.leftToCoord a b c x r s)
  left_toCoord_leftPure : ∀ a b c
      (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
      (z : (dD.algebra c).carrier) (m : dT.LeftCarrier a b c),
    dT.leftToCoord a b c (dT.leftRoute.leftPure a b c x y z m) =
      fun targetAB targetABC =>
        CData.rawFinSum (dD.algebra (a + b + c)) fun sourceAB =>
          CData.rawFinSum (dD.algebra (a + b + c)) fun sourceABC =>
            (dD.algebra (a + b + c)).mul
              (leftRouteCoeff dC a b c targetAB targetABC sourceAB sourceABC x y z)
              (dT.leftToCoord a b c m sourceAB sourceABC)
  left_toCoord_right : ∀ a b c (m : dT.LeftCarrier a b c)
      (x : (dD.algebra (a + b + c)).carrier),
    dT.leftToCoord a b c (dT.leftRoute.right a b c m x) = fun r s =>
      (dD.algebra (a + b + c)).mul (dT.leftToCoord a b c m r s) x

  right_toCoord_zero : ∀ a b c,
    dT.rightToCoord a b c (dT.rightRoute.zero a b c) =
      fun _ _ => (dD.algebra (a + b + c)).zero
  right_toCoord_add : ∀ a b c (x y : dT.RightCarrier a b c),
    dT.rightToCoord a b c (dT.rightRoute.add a b c x y) = fun r s =>
      (dD.algebra (a + b + c)).add
        (dT.rightToCoord a b c x r s) (dT.rightToCoord a b c y r s)
  right_toCoord_neg : ∀ a b c (x : dT.RightCarrier a b c),
    dT.rightToCoord a b c (dT.rightRoute.neg a b c x) = fun r s =>
      (dD.algebra (a + b + c)).neg (dT.rightToCoord a b c x r s)
  right_toCoord_smul : ∀ a b c q (x : dT.RightCarrier a b c),
    dT.rightToCoord a b c (dT.rightRoute.smul a b c q x) = fun r s =>
      (dD.algebra (a + b + c)).smul q (dT.rightToCoord a b c x r s)
  right_toCoord_component : ∀ a b c i (x : dT.RightCarrier a b c),
    dT.rightToCoord a b c (dT.rightRoute.component a b c i x) = fun r s =>
      (dD.algebra (a + b + c)).component
        (i + dC.rowParity b c r + dC.rowParity a (b + c) s)
        (dT.rightToCoord a b c x r s)
  right_toCoord_leftPure : ∀ a b c
      (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
      (z : (dD.algebra c).carrier) (m : dT.RightCarrier a b c),
    dT.rightToCoord a b c (dT.rightRoute.leftPure a b c x y z m) =
      fun targetBC targetABC =>
        CData.rawFinSum (dD.algebra (a + b + c)) fun sourceBC =>
          CData.rawFinSum (dD.algebra (a + b + c)) fun sourceABC =>
            (dD.algebra (a + b + c)).mul
              (rightRouteCoeff dC a b c targetBC targetABC sourceBC sourceABC x y z)
              (dT.rightToCoord a b c m sourceBC sourceABC)
  right_toCoord_right : ∀ a b c (m : dT.RightCarrier a b c)
      (x : (dD.algebra (a + b + c)).carrier),
    dT.rightToCoord a b c (dT.rightRoute.right a b c m x) = fun r s =>
      (dD.algebra (a + b + c)).mul (dT.rightToCoord a b c m r s) x

  hom_zero : ∀ a b c,
    dT.hom a b c (dT.leftRoute.zero a b c) = dT.rightRoute.zero a b c
  hom_add : ∀ a b c (x y : dT.LeftCarrier a b c),
    dT.hom a b c (dT.leftRoute.add a b c x y) =
      dT.rightRoute.add a b c (dT.hom a b c x) (dT.hom a b c y)
  hom_neg : ∀ a b c (x : dT.LeftCarrier a b c),
    dT.hom a b c (dT.leftRoute.neg a b c x) =
      dT.rightRoute.neg a b c (dT.hom a b c x)
  hom_smul : ∀ a b c r (x : dT.LeftCarrier a b c),
    dT.hom a b c (dT.leftRoute.smul a b c r x) =
      dT.rightRoute.smul a b c r (dT.hom a b c x)
  inv_zero : ∀ a b c,
    dT.inv a b c (dT.rightRoute.zero a b c) = dT.leftRoute.zero a b c
  inv_add : ∀ a b c (x y : dT.RightCarrier a b c),
    dT.inv a b c (dT.rightRoute.add a b c x y) =
      dT.leftRoute.add a b c (dT.inv a b c x) (dT.inv a b c y)
  inv_neg : ∀ a b c (x : dT.RightCarrier a b c),
    dT.inv a b c (dT.rightRoute.neg a b c x) =
      dT.leftRoute.neg a b c (dT.inv a b c x)
  inv_smul : ∀ a b c r (x : dT.RightCarrier a b c),
    dT.inv a b c (dT.rightRoute.smul a b c r x) =
      dT.leftRoute.smul a b c r (dT.inv a b c x)

  hom_right : ∀ a b c (m : dT.LeftCarrier a b c)
      (q : (dD.algebra (a + b + c)).carrier),
    dT.hom a b c (dT.leftRoute.right a b c m q) =
      dT.rightRoute.right a b c (dT.hom a b c m) q
  inv_right : ∀ a b c (m : dT.RightCarrier a b c)
      (q : (dD.algebra (a + b + c)).carrier),
    dT.inv a b c (dT.rightRoute.right a b c m q) =
      dT.leftRoute.right a b c (dT.inv a b c m) q
  hom_left : ∀ a b c i j k
      (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
      (z : (dD.algebra c).carrier) (m : dT.LeftCarrier a b c),
    (dD.algebra a).MemGrade i x →
    (dD.algebra b).MemGrade j y →
    (dD.algebra c).MemGrade k z →
    dT.hom a b c (dT.leftRoute.leftPure a b c x y z m) =
      dT.rightRoute.smul a b c
        (paritySign (dT.parity a b c * (i + j + k)))
        (dT.rightRoute.leftPure a b c x y z (dT.hom a b c m))
  inv_left : ∀ a b c i j k
      (x : (dD.algebra a).carrier) (y : (dD.algebra b).carrier)
      (z : (dD.algebra c).carrier) (m : dT.RightCarrier a b c),
    (dD.algebra a).MemGrade i x →
    (dD.algebra b).MemGrade j y →
    (dD.algebra c).MemGrade k z →
    dT.inv a b c (dT.rightRoute.leftPure a b c x y z m) =
      dT.leftRoute.smul a b c
        (paritySign (dT.parity a b c * (i + j + k)))
        (dT.leftRoute.leftPure a b c x y z (dT.inv a b c m))

  hom_component : ∀ a b c i (m : dT.LeftCarrier a b c),
    dT.hom a b c (dT.leftRoute.component a b c i m) =
      dT.rightRoute.component a b c (i + dT.parity a b c) (dT.hom a b c m)
  inv_component : ∀ a b c i (m : dT.RightCarrier a b c),
    dT.inv a b c (dT.rightRoute.component a b c i m) =
      dT.leftRoute.component a b c (i + dT.parity a b c) (dT.inv a b c m)
  hom_grade : ∀ a b c i (m : dT.LeftCarrier a b c),
    dT.leftRoute.MemGrade a b c i m →
      dT.rightRoute.MemGrade a b c (i + dT.parity a b c) (dT.hom a b c m)
  inv_grade : ∀ a b c i (m : dT.RightCarrier a b c),
    dT.rightRoute.MemGrade a b c i m →
      dT.leftRoute.MemGrade a b c (i + dT.parity a b c) (dT.inv a b c m)
  hom_inv_id : ∀ a b c (m : dT.RightCarrier a b c),
    dT.hom a b c (dT.inv a b c m) = m
  inv_hom_id : ∀ a b c (m : dT.LeftCarrier a b c),
    dT.inv a b c (dT.hom a b c m) = m

/-- A completed explicit raw connector over completed `D` and `C`. -/
structure T (D : D) (C₀ : C D) where
  data : TData D.data C₀.data
  laws : TLaws D.data D.laws C₀.data C₀.laws data

end Superfusion.RMod.RawDCT
