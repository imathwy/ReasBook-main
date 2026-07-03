import Mathlib
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap04.Definition_4_27_20

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [ObjectProperty.IsTriangulated P]

/- Domain-style sampling for Lemma `13.6.6`.
- primary domain: saturated compatible multiplicative systems arising from triangulated object
  properties in a triangulated category;
- sampled owner declarations:
  `P.isoClosure.trW`,
  `P.trW`,
  `P.trW_isoClosure`,
  `P.isoClosure.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `P.IsStableUnderRetracts`,
  `P.trW.IsMultiplicative`,
  `P.trW.IsCompatibleWithTriangulation`;
- best owner abstraction: the source-facing morphism-property owner is `P.isoClosure.trW`,
  attached to the strictly full triangulated subcategory `P.isoClosure`; `P.trW` is only the
  bridge view provided by `P.trW_isoClosure`;
- source/core/bridge triage:
  `source-facing`: the Stacks saturation condition for the strictly full triangulated subcategory
    attached to `P`, i.e. `P.isoClosure`, together with its canonical Verdier morphism property
    `P.isoClosure.trW`;
  `core/canonical`: the owners `P.isoClosure.trW`, `ObjectProperty.isoClosure`, and
    `ObjectProperty.IsStableUnderRetracts`;
  `bridge/view`: the comparison `P.trW_isoClosure` and the derived reformulation using `P.trW`,
    with the iso-closed specialization as a companion.
- primitive data: the triangulated object property `P`;
- derived API: the multiplicative-system and triangulation-compatibility instances on `P.trW`,
  the iso-closure `P.isoClosure`, the owner theorem on `P.isoClosure.trW`, and its iso-closed
  specialization on `P.trW`.

No extra local wrapper is needed here: the owner-level theorem should use `P.isoClosure.trW`
directly, and the iso-closed `P.trW` formulation should be derived from it rather than exposed
through an extra intermediate bridge theorem.
-/

/- Companion recall: for a triangulated object property `P`, the cone-defined morphism property
`P.trW` is already a multiplicative system by the canonical `trW` instance. -/
#check (inferInstance : MorphismProperty.IsMultiplicative P.trW)

/- Companion recall: for a triangulated object property `P`, the cone-defined morphism property
`P.trW` is already compatible with the triangulated structure by the canonical `trW` instance. -/
#check (inferInstance : MorphismProperty.IsCompatibleWithTriangulation P.trW)

-- Proof sketch: for the forward implication, use the saturation axiom for `P.isoClosure.trW` on
-- the standard distinguished triangles attached to a biproduct decomposition to show that
-- `P.isoClosure` is stable under retracts. For the reverse implication, follow the octahedral
-- argument from the text: if `f ≫ g` and `g ≫ h` lie in `P.isoClosure.trW`, then the cones of
-- these composites lie in `P.isoClosure`; use the octahedron to relate these cones to a cone of
-- `g`, and apply retract stability to conclude that the cone of `g` also lies in `P.isoClosure`.
/-- Lemma 13.6.6: for a triangulated object property `P` on a triangulated category `D`, the
canonical Verdier morphism property attached to the strictly full triangulated subcategory
`P.isoClosure`, namely `P.isoClosure.trW`, is a saturated multiplicative system if and only if
`P.isoClosure` is stable under retracts. -/
theorem isoClosure_trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts :
    IsSaturatedMultiplicativeSystem P.isoClosure.trW ↔ P.isoClosure.IsStableUnderRetracts := sorry

/-- If `P` is already closed under isomorphisms, Lemma 13.6.6 specializes to retract stability of
`P` itself. -/
theorem trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts
    [P.IsClosedUnderIsomorphisms] :
    IsSaturatedMultiplicativeSystem P.trW ↔ P.IsStableUnderRetracts := by
  simpa only [P.trW_isoClosure, P.isoClosure_eq_self] using
    (isoClosure_trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts P)

/-- If `P` is stable under retracts, then the cone-defined morphism property `P.trW` is a
saturated multiplicative system. -/
theorem trW_isSaturatedMultiplicativeSystem [P.IsStableUnderRetracts] :
    IsSaturatedMultiplicativeSystem P.trW :=
  (trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts P).2 inferInstance

instance [P.IsStableUnderRetracts] : IsSaturatedMultiplicativeSystem P.trW :=
  trW_isSaturatedMultiplicativeSystem P

end

end CategoryTheory
