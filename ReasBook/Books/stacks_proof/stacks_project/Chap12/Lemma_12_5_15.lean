import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 12.5.15:
- primary domain: exactness criteria for short complexes in abelian categories, expressed by
  lifting morphisms after refinement by an epimorphism;
- inspected owner declarations:
  `ShortComplex.Exact`,
  `ShortComplex.exact_iff_exact_toComposableArrows`,
  `ShortComplex.exact_iff_exact_up_to_refinements`,
  `ShortComplex.Exact.exact_up_to_refinements`;
- best owner abstraction: `ShortComplex C` with the owner predicate `S.Exact`; the refinement
  criterion is derived API already owned upstream by
  `ShortComplex.exact_iff_exact_up_to_refinements`, and the pointwise lifting form is the
  theorem-level view rather than new primitive data;
- primitive data: the short complex `S`;
- derived API: the refinement-lifting characterization of `S.Exact` and the forward lifting
  operation exposed by `ShortComplex.Exact.exact_up_to_refinements`.

Source/core/bridge triage:
- `source-facing`: the textbook criterion that `x₁ ⟶ x₂ ⟶ x₃` is exact iff every morphism into the
  middle term killed by the second map lifts through the first map after refining the source by an
  epimorphism;
- `core/canonical`: the owner predicate `ShortComplex.Exact`;
- `bridge/view`: `ShortComplex.exact_iff_exact_up_to_refinements`, which is already the exact
  canonical bridge theorem for this criterion.

This file should stay recall-only: the source statement is already owned upstream with the correct
short-complex abstraction, so a local restatement or wrapper would only duplicate the API.
-/

variable {C : Type u} [Category.{v} C] [Abelian C]

/- Lemma 12.5.15: in an abelian category, a short complex is exact if and only if every morphism
into the middle object that is killed by the second map lifts through the first map after
precomposition by some epimorphism. Applied to `ShortComplex.mk f g h`, this is exactly the
textbook criterion for the exactness of `x ⟶ y ⟶ z`. -/
recall ShortComplex.exact_iff_exact_up_to_refinements (S : ShortComplex C) :
    S.Exact ↔
      ∀ ⦃A : C⦄ (x₂ : A ⟶ S.X₂) (_ : x₂ ≫ S.g = 0),
        ∃ (A' : C) (π : A' ⟶ A) (_ : Epi π) (x₁ : A' ⟶ S.X₁), π ≫ x₂ = x₁ ≫ S.f

end CategoryTheory
