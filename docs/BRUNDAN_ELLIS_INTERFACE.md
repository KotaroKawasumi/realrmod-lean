# Category interface and tensor conventions

The declaration surface in [Challenge.lean](../Challenge.lean) fixes real super
vector spaces as the enriching category. The completed implementations are
available through [Solution.lean](../Solution.lean).

## Structures

`SuperVec` is the category of `ZMod 2`-graded real vector spaces. Its symmetry is
the Koszul symmetry. `SuperCategory` and `SuperFunctor` use Mathlib's enriched
categories and enriched functors. `Even C` is the category obtained by forgetting
the enrichment.

The monoidal structure records the tensor on objects and morphisms, and its
compatibility with the even monoidal category. Naturality is required in every
degree. A Pi structure supplies a parity object and mutually inverse odd maps
between that object and the unit. The fusion hypotheses and weak pointedness
are the ones specified in this interface, using Mathlib's selected right dual.

[Classification.lean](../RMod/BrundanEllis/Classification.lean) transfers the
classification through proved parity, dual, gauge and monoidal conversions.
The public surface's 48 registered targets also include stacking and the group
structure. Their exact statements and construction types are listed in
[comparator.json](../comparator.json).

## Composition and signs

Lean's `f ≫ f'` applies `f` first and then `f'`. Mathlib's enriched composition
takes `Hom(X,Y) ⊗ Hom(Y,Z)` in that chronological order.

For homogeneous `f`, `g`, `f'`, `g'` of degrees `a`, `b`, `c`, `d`, the product
enrichment's interchange sign is `(-1)^(b*c)`. The corresponding paper convention
uses `(-1)^(a*d)` in the same chronological ordering of the variables. The two
tensor conventions are related by

```text
tensor_chron(f, g) = (-1)^(a*b) • tensor_paper(f, g).
```

This preserves the even tensor, associators and unitors. The conversion is proved
in [TensorConvention.lean](../RMod/Hierarchy/Bridge/TensorConvention.lean).

## Construction holes

The specification intentionally contains registered construction and theorem
holes. Fixed type fields and `*_data` statements constrain the foundational
operations. `realRMod` and `twistedPullback` are construction targets: their types
and stated properties are checked, without prescribing a unique implementation.
The proof library supplies actual values and proofs and does not import the
specification. See [verification details](VERIFICATION.md) for the precise checks.
