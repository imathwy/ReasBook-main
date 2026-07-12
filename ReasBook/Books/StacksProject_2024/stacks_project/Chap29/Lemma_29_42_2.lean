import Mathlib.AlgebraicGeometry.ValuativeCriterion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the canonical owners
-- `ValuativeCriterion.Existence`, `ValuativeCriterion.Uniqueness`,
-- `UniversallyClosed.of_valuativeCriterion`, and `IsSeparated.valuativeCriterion`. The source
-- hypothesis is kept as a restricted valuative lifting condition: the generic map in a
-- `ValuativeCommSq f` must factor through the dense quasi-compact map `h : U ⟶ X`.

/-- Lemma 29.42.2 (1): let `f : X ⟶ S` and `h : U ⟶ X` be quasi-compact morphisms of schemes
with dense image for `h`. Suppose that for every valuative commutative square for `f` whose
generic arrow factors through `h`, there exists a unique dotted arrow making the square commute.
Then `f` is universally closed. -/
@[stacks 0894]
theorem universallyClosed_of_existsUnique_valuative_lift_from_denseRange
    {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [QuasiCompact f] [QuasiCompact h]
    (h_dense : DenseRange h)
    (h_valuative : ∀ T : ValuativeCommSq f,
      (∃ g : Spec (CommRingCat.of T.K) ⟶ U, g ≫ h = T.i₁) →
        Nonempty (Unique T.commSq.LiftStruct)) :
    UniversallyClosed f := sorry

/-- Lemma 29.42.2 (2): under the hypotheses of Lemma 29.42.2, if `f` is also quasi-separated,
then `f` is separated. -/
@[stacks 0894]
theorem isSeparated_of_existsUnique_valuative_lift_from_denseRange
    {U X S : Scheme.{u}} (f : X ⟶ S) (h : U ⟶ X)
    [QuasiCompact f] [QuasiCompact h] [QuasiSeparated f]
    (h_dense : DenseRange h)
    (h_valuative : ∀ T : ValuativeCommSq f,
      (∃ g : Spec (CommRingCat.of T.K) ⟶ U, g ≫ h = T.i₁) →
        Nonempty (Unique T.commSq.LiftStruct)) :
    IsSeparated f := sorry

end AlgebraicGeometry
