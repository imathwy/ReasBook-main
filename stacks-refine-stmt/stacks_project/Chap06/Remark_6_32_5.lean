import Mathlib
import stacks_project.Chap06.ClosedSubsetInclusion

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits TopCat TopologicalSpace
open TopCat.Sheaf

universe u

section

variable {X : TopCat.{u}} {Z : Set X}

/- Domain-style sampling for Remark 6.32.5:
- primary domain: right exactness of sheaf pushforward along the inclusion of a closed subset of a
  topological space;
- sampled owner declarations:
  `TopCat.closedSubsetInclusion`,
  `Sheaf.pushforward`,
  `rightExactFunctor`,
  `rightExactFunctor_iff`;
- owner abstraction: the chapter owner is
  `rightExactFunctor _ _ (Sheaf.pushforward (Type u) iZ)`, built from the canonical inclusion
  `TopCat.closedSubsetInclusion X Z`;
- primitive data: the ambient space `X`, the closed subset `Z`, the properness witness
  `Z ≠ Set.univ`, and the functor `Sheaf.pushforward (Type u) iZ`;
- derived API: failure to preserve binary coproducts as the witness, the equivalent
  finite-colimit formulation via `rightExactFunctor_iff`, and the consequence that pushforward has
  no right adjoint.

Source/core/bridge triage:
- `source-facing`: the Stacks-project remark that pushforward from a proper closed subset is not
  right exact on sheaves of sets;
- `core/canonical`: `rightExactFunctor _ _ (Sheaf.pushforward (Type u) iZ)`;
- `bridge/view`: the binary-coproduct obstruction, the reformulation via
  `PreservesFiniteColimits`, and the no-right-adjoint consequence. -/

local notation "iZ" => X.closedSubsetInclusion Z

-- Proof sketch: evaluate pushforward at a point `x ∉ Z`. By Lemma 6.32.1 the stalk there is
-- terminal, so the pushforward of the coproduct of two copies of the terminal sheaf has one-point
-- stalk at `x`, whereas the coproduct of the two pushforward sheaves has two-point stalk there.
-- Since stalk functors preserve finite colimits, pushforward cannot preserve that coproduct.
/-- Remark 6.32.5 (1): if `i : Z ↪ X` is the inclusion of a proper closed subset, then pushforward on
sheaves of sets along `i` does not preserve binary coproducts. The Stacks argument tests the
coproduct of two copies of the terminal sheaf. -/
theorem closedSubsetTypeSheafPushforward_not_preservesBinaryCoproducts
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ PreservesColimitsOfShape (Discrete WalkingPair) (Sheaf.pushforward (Type u) iZ) := by
  sorry

/-- Remark 6.32.5 (2): if `i : Z ↪ X` is the inclusion of a proper closed subset, then pushforward on
sheaves of sets along `i` is not right exact. The binary-coproduct obstruction above is the
source-facing witness for the canonical owner predicate `rightExactFunctor`. -/
theorem closedSubsetTypeSheafPushforward_not_rightExact
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ rightExactFunctor _ _ (Sheaf.pushforward (Type u) iZ) := by
  intro hright
  let _ : PreservesFiniteColimits (Sheaf.pushforward (Type u) iZ) := by
    simpa [rightExactFunctor_iff] using hright
  exact closedSubsetTypeSheafPushforward_not_preservesBinaryCoproducts hZ hproper inferInstance

/-- Companion bridge for Remark 6.32.5: pushforward on sheaves of sets along the inclusion of a
proper closed subset does not preserve finite colimits. This is just
`closedSubsetTypeSheafPushforward_not_rightExact` rewritten through `rightExactFunctor_iff`. -/
theorem closedSubsetTypeSheafPushforward_not_preservesFiniteColimits
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ PreservesFiniteColimits (Sheaf.pushforward (Type u) iZ) := by
  simpa [rightExactFunctor_iff] using
    (closedSubsetTypeSheafPushforward_not_rightExact hZ hproper)

-- Proof sketch: a left adjoint preserves all colimits, hence is right exact. Apply the owner-level
-- obstruction above to the pushforward functor along the proper closed-subset inclusion.
/-- Pushforward on sheaves of sets along the inclusion of a proper closed subset has no right
adjoint. -/
theorem closedSubsetTypeSheafPushforward_not_isLeftAdjoint
    (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ¬ (Sheaf.pushforward (Type u) iZ).IsLeftAdjoint := by
  intro hleft
  let _ : (Sheaf.pushforward (Type u) iZ).IsLeftAdjoint := hleft
  exact
    closedSubsetTypeSheafPushforward_not_rightExact hZ hproper
      (by
        simpa [rightExactFunctor_iff] using
          (inferInstance : PreservesFiniteColimits (Sheaf.pushforward (Type u) iZ)))

end
