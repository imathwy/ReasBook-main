import Mathlib
import stacks_project.Chap13.Lemma_13_34_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

attribute [local instance] HasDerivedCategory.standard

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
  [HasCountableProducts 𝒜] [CountableAB4Star 𝒜] [EnoughInjectives 𝒜]

local instance isInjective_containsZero : (isInjective 𝒜).ContainsZero where
  exists_zero := ⟨0, Limits.isZero_zero 𝒜, inferInstance⟩

local instance isInjective_hasMonoEmbedding : HasMonoEmbedding (isInjective 𝒜) where
  exists_mono X := ⟨Injective.under X, inferInstance, Injective.ι X, inferInstance⟩

local instance isInjective_isClosedUnderFiniteProducts :
    (isInjective 𝒜).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J := by
    refine ⟨?_⟩
    intro X hX
    rcases hX with ⟨hX⟩
    let f : J → 𝒜 := fun j ↦ hX.diag.obj (Discrete.mk j)
    let _ : ∀ j : J, Injective (f j) := fun j ↦ hX.prop_diag_obj (Discrete.mk j)
    let _ : Injective (∏ᶜ f) := inferInstance
    let e : ∏ᶜ f ≅ X :=
      Pi.isoLimit hX.diag ≪≫ (hX.isLimit.conePointUniqueUpToIso (limit.isLimit hX.diag)).symm
    exact Injective.of_iso e inferInstance

/- Domain-style sampling for Lemma 13.34.7:
- primary domain: K-injective resolutions of cochain complexes in an abelian category with enough
  injectives and exact countable products;
- sampled owner declarations:
  `CountableAB4Star`,
  `CountableAB4Star.ofShape`,
  `CountableAB4Star.of_hasExactLimitsOfShape_nat`,
  `CategoryTheory.isInjective`,
  `LowerTruncationResolutionSystem`,
  `LowerTruncationResolutionSystem.intoLimit`,
  `isKInjective_lowerTruncationResolutionSystemLimit`,
  `lowerTruncationResolutionLimit_quasiIso_iff_isIso_derivedComparison`;
- best owner abstraction: for the exact-product hypothesis, the source-facing owner is
  `CountableAB4Star 𝒜`; `HasExactLimitsOfShape (Discrete ℕ) 𝒜` is only a bridge recovered from it
  by `CountableAB4Star.ofShape ℕ`. For the resolution data, the canonical map is `S.intoLimit`
  from a chosen lower truncation resolution system `S` to its inverse-limit complex; the
  source-facing theorem should expose only the resulting K-injective complex and quasi-isomorphism,
  not the auxiliary resolution-system data;
- primitive-vs-derived split:
  primitive data: the source complex `K` and the ambient hypotheses `EnoughInjectives` plus
    exact countable products, canonically expressed by `[HasCountableProducts 𝒜]` and
    `[CountableAB4Star 𝒜]`;
  derived API: the chosen lower truncation resolution system, its limit complex `limit S.diagram`,
  the K-injectivity theorem for that limit, and the canonical map `S.intoLimit`.

Source/core/bridge triage:
- `source-facing`: existence of a quasi-isomorphism from `K^•` to a K-injective complex;
- `core/canonical`: `CountableAB4Star 𝒜` for exact countable products, and
  `LowerTruncationResolutionSystem.intoLimit` together with
  `isKInjective_lowerTruncationResolutionSystemLimit` for the resolution construction;
- `bridge/view`: `CountableAB4Star.ofShape ℕ` as the local bridge to
  `HasExactLimitsOfShape (Discrete ℕ) 𝒜`, and the quasi-isomorphism claim for `S.intoLimit`,
  reduced in Lemma 13.34.6 to the corresponding derived-limit comparison statement. -/

-- Proof sketch: choose a lower truncation resolution system by injective objects from
-- `exists_lowerTruncationResolutionSystem`, form its inverse-limit complex, and use
-- `isKInjective_lowerTruncationResolutionSystemLimit` to see that the target is K-injective.
-- Lemma 13.34.6 reduces the quasi-isomorphism claim to showing that
-- `K ⟶ R lim_n τ_{\ge -(n + 1)} K` is an isomorphism in the derived category, which follows from
-- the Milnor triangle together with exactness of countable products, used through the canonical
-- owner `[CountableAB4Star 𝒜]` as in Lemma 13.34.2.
/-- Lemma 13.34.7: if an abelian category has enough injectives and exact countable products, then
every cochain complex admits a quasi-isomorphism to a K-injective complex. -/
theorem exists_quasiIso_to_kInjective
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (f : K ⟶ I), QuasiIso f := by
  obtain ⟨S⟩ := exists_lowerTruncationResolutionSystem (isInjective 𝒜) K
  refine ⟨limit S.diagram, isKInjective_lowerTruncationResolutionSystemLimit S, S.intoLimit, ?_⟩
  sorry

end

end CategoryTheory
