import Mathlib
import StacksProject_2024.Chap13.Lemma_13_26_6

open CategoryTheory
open CategoryTheory.ObjectProperty
open CochainComplex
open FilteredObject.Hom

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable [Abelian (finiteFilteredObjectCat 𝒜)]

local notation "FilF" => Fil^f(𝒜)
local notation "single₀" => CochainComplex.singleFunctor FilF (0 : ℤ)

/- Domain-style sampling for Lemma `13.26.7`.
- primary domain: strict lifting of morphisms along filtered quasi-isomorphisms into bounded-below
  filtered-injective cochain complexes in `Fil^f(𝒜)`;
- sampled owner declarations:
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    .exists_strict_lift_to_boundedBelow_filteredInjective`,
  `finiteFilteredObjectAssociatedGradedCochainFunctor`,
  `FilteredObject.Hom.Strict`,
  `CategoryTheory.CommSq`;
- best owner abstraction: the bounded-below filtered-injective complexes are canonically owned by
  `CochainComplex.FilteredInjectivePlus 𝒜`; the source comparison map
  `K ⟶ I^•` together with its associated-graded quasi-isomorphism and degreewise strictness is
  canonically owned by the chapter declaration
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`; its primitive bounded-below
  termwise-monomorphic part is the generic Chapter 13 owner
  `CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`; the degree-zero square-shaped formulation
  is a source-facing bridge owned by `CategoryTheory.CommSq`;
- primitive data: a cochain complex `K`, owner objects `I J` in
  `CochainComplex.FilteredInjectivePlus 𝒜`, a source comparison morphism `α : K ⟶ I^•` carrying
  the owner data
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I α`, together with a target
  comparison map `γ : K ⟶ J^•`;
- derived API: the degree-zero commutative square corollary on the underlying cochain complexes
  via the canonical coercion, with the source hypotheses kept in the same primitive owner/data
  split as in `Lemma_13_26_6`, and obtained directly from the owner theorem
  `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
    .exists_strict_lift_to_boundedBelow_filteredInjective`;
- source/core/bridge triage:
  `source-facing`: the degree-zero square corollary below;
  `core/canonical`: `CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso`,
    `CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`,
    `CochainComplex.FilteredInjectivePlus`,
    `finiteFilteredObjectAssociatedGradedCochainFunctor`, and `FilteredObject.Hom.Strict`;
  `bridge/view`: the canonical coercion from `CochainComplex.FilteredInjectivePlus 𝒜` to
    `CochainComplex (Fil^f(𝒜)) ℤ`, and the source-facing `CommSq` wrapper for the single-degree
    statement.

The public surface therefore keeps the bounded-below filtered-injective complexes on the canonical
owner `CochainComplex.FilteredInjectivePlus 𝒜` and reuses the primitive comparison-map owner
`CochainComplex.IsTermwiseMonoStrictlyGEWithTermsIn`, but takes the full filtered comparison datum
through the existing chapter owner
`CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso` instead of restating its derived
fields as parallel arguments. -/

variable {A B : FilF}

-- Proof sketch: argue by the filtered comparison theorem for bounded-below filtered-injective
-- complexes, using the full comparison datum `ha` supplied by Lemma `13.26.6`. Specialize to
-- `K = A[0]` and `γ = (single₀).map f ≫ b`, then package the resulting equality as a commutative
-- square.
/-- Lemma 13.26.7: a morphism in `Fil^f(𝒜)` extends from a bounded-below filtered-injective
resolution `A[0] ⟶ I^•` with termwise strict degree maps to a bounded-below filtered-injective
complex `J^•` equipped with a comparison map `B[0] ⟶ J^•`. -/
theorem exists_cochainMap_of_filteredQuasiIso_to_termwise_filteredInjective
    {I J : CochainComplex.FilteredInjectivePlus 𝒜}
    (f : A ⟶ B) (a : (single₀).obj A ⟶ I)
    (_ha : CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso 0 I a)
    (b : (single₀).obj B ⟶ J) :
    ∃ g : I ⟶ J, CommSq a ((single₀).map f) g b :=
  let ha := _ha
  -- Apply the comparison theorem from Lemma `13.26.6` to the morphism `A[0] ⟶ J`.
  match
      CochainComplex.IsTermwiseStrictMonoStrictlyGEFilteredQuasiIso
        .exists_strict_lift_to_boundedBelow_filteredInjective ha ((single₀).map f ≫ b) with
  | ⟨g, hg⟩ =>
      -- Package the resulting equality as the required commutative square.
      ⟨g, hg⟩

end CategoryTheory
