import Mathlib
import StacksProject_2024.Chap13.Lemma_13_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits

universe w v u

-- Semantic search note: `lean_leansearch` is unavailable in this runner, so the owner/API choice
-- was checked against the Chapter 24 recall files `Definition_24_21_1`, `Definition_24_21_2`, and
-- the Chapter 13 product theorem `CategoryTheory.isKInjective_of_product`.

/- Domain-style sampling for Lemma 24.25.8:
- primary domain: K-injective differential graded modules over a sheaf of differential graded
  algebras on a ringed site;
- sampled owner declarations:
  `CochainComplex.IsKInjective`,
  `HasProduct`,
  `∏ᶜ I`;
- best owner abstraction: Chapter 24 uses differential graded `\mathcal A`-modules through the
  canonical cochain-complex owner, so the source statement should be expressed as K-injectivity of
  the categorical product complex in the ambient abelian category of graded `\mathcal A`-modules;
- primitive data: the index set `T`, the family `ℐ`, the product existence hypothesis
  `[HasProduct ℐ]`, and the K-injective hypotheses `[∀ t, (ℐ t).IsKInjective]`;
- derived API: the product complex `(∏ᶜ ℐ)` is K-injective.

Source/core/bridge triage:
- `source-facing`: `DifferentialGradedModule.product_isKInjective`;
- `core/canonical`: `CochainComplex.IsKInjective` and the categorical product owner `∏ᶜ`;
- `bridge/view`: the chapter-local observation that a differential graded `\mathcal A`-module is
  represented via the ambient cochain-complex category, so no extra ringed-site wrapper is needed.
-/

namespace DifferentialGradedModule

/-- Lemma 24.25.8: for a family of K-injective differential graded `\mathcal A`-modules on a
ringed site, their product is again K-injective. In Chapter 24 this is expressed through the
canonical cochain-complex owner on the ambient abelian category of graded `\mathcal A`-modules. -/
@[stacks 0FSV]
theorem product_isKInjective
    {GrModA : Type u} [Category.{v} GrModA] [Abelian GrModA]
    {T : Type w} (ℐ : T → CochainComplex GrModA ℤ)
    [HasProduct ℐ] [∀ t, (ℐ t).IsKInjective] :
    (∏ᶜ ℐ).IsKInjective :=
by
  let π : ∀ t, ∏ᶜ ℐ ⟶ ℐ t := fun t ↦ Pi.π ℐ t
  have hπ : IsLimit (Fan.mk (∏ᶜ ℐ) π) := by
    simpa [π] using productIsProduct ℐ
  exact CategoryTheory.isKInjective_of_product π hπ

end DifferentialGradedModule
