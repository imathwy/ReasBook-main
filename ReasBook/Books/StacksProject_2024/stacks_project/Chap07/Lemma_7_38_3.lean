import Mathlib
import StacksProject_2024.Chap07.Lemma_7_38_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.ObjectProperty

universe w v u w'

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Layering for Lemma 7.38.3:
- primary domain: conservative families of points of a site and their detection of equality of
  sections through point fibers;
- sampled owner declarations:
  `ObjectProperty.IsConservativeFamilyOfPoints`,
  `isConservativePointFamily_iff`,
  `JointlyFaithful.jointlyReflectsIsomorphisms`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`;
- source/core/bridge triage:
  `source-facing`: the textbook criterion that distinct local sections are separated by some germ
    at a point of the family;
  `core/canonical`: `(ofObj p).IsConservativeFamilyOfPoints`;
  `bridge/view`: the indexed-family recall `isConservativePointFamily_iff`, together with the
    sheafified-representable Yoneda equivalence used to compare sections with morphisms out of
    `h[U]^#[J]`.
- primitive data: only the indexed family of points `p`;
- derived API here: the source-facing separation criterion.

The owner abstraction remains `(ofObj p).IsConservativeFamilyOfPoints`; this file should stay a
thin source-facing bridge, not a second owner for conservative point families.
-/

-- Proof sketch: for the forward implication, if two sections have the same germ at every point of
-- the family, apply conservativity to the corresponding morphisms `h[U]^#[J] ⟶ ℱ`, using
-- `uliftSheafifiedRepresentableHomEquiv` to pass between sections and sheaf morphisms and the
-- canonical point-fiber comparison for sheafified representables. For the converse, use the
-- separation hypothesis to show the stalk family is jointly faithful on sheaves of sets; then the
-- generic owner theorem `JointlyFaithful.jointlyReflectsIsomorphisms`, combined with
-- `isConservativePointFamily_iff`, upgrades that joint faithfulness to conservativity.
/-- Lemma 7.38.3: a family of points of a site is conservative if and only if every pair of
distinct local sections of a set-valued sheaf is separated by their germs at some point of one of
the fibers `u_i(U)`. -/
theorem isConservativePointFamily_iff_exists_point_separating_sections
    {ι : Type w} (p : ι → Point.{w'} J) :
    (ofObj p).IsConservativeFamilyOfPoints ↔
      ∀ ⦃ℱ : Sheaf J (Type (max u v w'))⦄ (U : C) (s s' : ℱ.obj.obj (op U)),
        s ≠ s' →
          ∃ i : ι, ∃ x : (p i).fiber.obj U,
            (p i).toPresheafFiber U x ℱ.obj s ≠ (p i).toPresheafFiber U x ℱ.obj s' := by
  sorry

end GrothendieckTopology

end CategoryTheory
