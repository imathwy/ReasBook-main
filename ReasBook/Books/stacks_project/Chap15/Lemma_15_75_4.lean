import stacks_project.Chap15.Definition_15_75_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)

/- Domain-style sampling for Lemma 15.75.4:
- primary domain: perfect objects in the derived category `D(R)` as an object property and their
  behavior with respect to distinguished triangles;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CochainComplex.IsBoundedFiniteProjective`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsStableUnderShift`;
- best owner abstraction: the canonical owner is the object property `PerfectObj`, and this file
  should expose its `ObjectProperty.IsTriangulated` instance directly rather than introducing a
  parallel eta-expanded surface for the same object property;
- primitive vs. derived:
  primitive data are the perfectness predicate `DerivedCategory.IsPerfect` and its defining
  bounded finite-projective representatives from Definition `15.75.1`;
  derived API is the triangulated closure statement for the perfectness object property;
- source/core/bridge triage:
  `source-facing`: the textbook two-out-of-three statement for perfect complexes in distinguished
    triangles;
  `core/canonical`: `ObjectProperty.IsTriangulated PerfectObj`;
  `bridge/view`: concrete bounded finite-projective representatives witnessing perfectness.

This file targets the `core/canonical` layer so downstream files can reuse the owner instance
directly instead of redeclaring parallel local copies.
-/
-- Proof sketch: use the canonical owner-level two-out-of-three statement for perfect complexes in
-- distinguished triangles, regarding perfectness as the object property on `D(R)` defined by
-- bounded finite-projective representatives.
/-- Lemma 15.75.4: the object property of being a perfect complex in `D(R)` is triangulated.
Equivalently, in a distinguished triangle of `D(R)`, if two of the three objects are perfect,
then so is the third. -/
instance perfectObjectProperty_isTriangulated :
    ObjectProperty.IsTriangulated PerfectObj := by
  sorry

end

end CategoryTheory
