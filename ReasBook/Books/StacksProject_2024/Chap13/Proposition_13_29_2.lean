import Mathlib
import stacks_project.Chap12.Definition_12_5_3
import stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ] [HasDerivedCategory.{w} ℬ]

variable (F : 𝒜 ⥤ ℬ) [PreservesFiniteColimits F]

local instance : PreservesBinaryBiproducts F :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts F

local instance : F.Additive := Functor.additive_of_preservesBinaryBiproducts F

variable (P : ObjectProperty 𝒜)
  [P.ContainsZero] [P.IsClosedUnderFiniteCoproducts] [HasEpiCover P]
  [HasColimitsOfShape ℕ 𝒜] [HasColimitsOfShape ℕ ℬ]
  [HasExactColimitsOfShape ℕ 𝒜] [HasExactColimitsOfShape ℕ ℬ]
  [PreservesColimitsOfShape ℕ F]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F

/- Domain-style sampling for Proposition 13.29.2:
- primary domain: unbounded left derived functors of additive functors, built from bounded-above
  acyclic resolutions and exact sequential colimits;
- sampled owner declarations:
  `Functor.HasPointwiseLeftDerivedFunctor`,
  `Functor.hasLeftDerivedFunctor_of_hasPointwiseLeftDerivedFunctor`,
  `UpperTruncationResolutionTower`,
  `Functor.hasPointwiseLeftDerivedFunctor_of_subset`;
- best owner abstraction: the canonical owner is
  `Functor.HasPointwiseLeftDerivedFunctor KtoD Qis`; the total left derived functor is then the
  standard bridge/view consequence;
- primitive-vs-derived split:
  primitive data: `P`, the bounded-above acyclicity hypothesis `hFacyclic`, and the exact
    sequential-colimit assumptions on `𝒜`, `ℬ`, and `F`;
  derived API: pointwise left-derived existence for `KtoD`, and then the total left derived
    functor by the canonical instance.

Source/core/bridge triage:
- `source-facing`: the proposition that `LF` is defined on all of `D(\mathcal A)`;
- `core/canonical`: `Functor.HasPointwiseLeftDerivedFunctor KtoD Qis`;
- `bridge/view`: the corollary upgrading the pointwise owner to
  `Functor.HasLeftDerivedFunctor KtoD Qis`.
-/

-- Proof sketch: use Lemma `13.15.4` to resolve each bounded-above truncation by a bounded-above
-- complex of objects in `P`, and Lemma `13.29.1` to assemble these into a sequential system whose
-- colimit is quasi-isomorphic to the original complex. The hypothesis `hFacyclic` shows that the
-- bounded-above stages compute the bounded-above left derived functor, while exact sequential
-- colimits in `𝒜` and `ℬ` and preservation of those colimits by `F` upgrade this computation from
-- bounded-above complexes to arbitrary complexes. Then apply the pointwise-to-total criterion for
-- left derived functors.
/-- Under the hypotheses of Proposition 13.29.2, the unbounded functor
`K(\mathcal A) ⟶ D(\mathcal B)` has a pointwise left derived functor at every object. This is the
canonical owner-level formulation; the source-facing proposition below is its standard corollary.
-/
theorem hasPointwiseLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic) :
    Functor.HasPointwiseLeftDerivedFunctor KtoD Qis := sorry

/-- Proposition 13.29.2: let `F : 𝒜 ⥤ ℬ` be a right exact functor of abelian categories, and let
`P` be an object property on `𝒜` containing `0`, closed under finite direct sums, and admitting
an objectwise epimorphic cover of every object. Assume every bounded-above acyclic cochain
complex with terms in `P` is sent by `F` to an acyclic complex, that `𝒜` and `ℬ` have exact
sequential colimits, and that `F` preserves sequential colimits. Then the left derived functor
`LF` is defined on all of `D(𝒜)`. -/
theorem hasLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
    (hFacyclic :
      ∀ (K : CochainComplex 𝒜 ℤ) (_ : CochainComplex.minus 𝒜 K) (_ : K.Acyclic)
        (_ : ∀ i : ℤ, P (K.X i)),
        ((F.mapHomologicalComplex (up ℤ)).obj K).Acyclic) :
    Functor.HasLeftDerivedFunctor KtoD Qis := by
  let _ : Functor.HasPointwiseLeftDerivedFunctor KtoD Qis :=
    hasPointwiseLeftDerivedFunctor_of_boundedAbove_acyclic_property_and_exact_sequential_colimits
      F P hFacyclic
  infer_instance

end

end CategoryTheory
