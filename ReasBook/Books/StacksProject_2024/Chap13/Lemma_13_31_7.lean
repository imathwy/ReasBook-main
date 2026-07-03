import Mathlib
import StacksProject_2024.Chap13.Lemma_13_14_14

-- Declarations for this item will be appended below by the statement pipeline.

open ComplexShape

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒟']
  [Abelian 𝒜]

local notation "KHom" => HomotopyCategory 𝒜 (up ℤ)
local notation "W" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.31.7:
- primary domain: right derived functors on the unbounded homotopy category `K(\mathcal A)`,
  obtained from K-injective replacements;
- sampled owner declarations:
  `kInjective_computesRightDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`,
  `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`,
  `Functor.ComputesRightDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctor`;
- best owner abstractions:
  `source-facing`: the existence of right derived functors on `K(\mathcal A)` under
    K-injective replacements;
  `core/canonical`: `Functor.ComputesRightDerivedAt`,
    `Functor.HasPointwiseRightDerivedFunctor`, the Chapter `13` owner bridge
    `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`, and the
    globalization owner theorem `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`;
  `bridge/view`: the K-injective computation theorem
    `kInjective_computesRightDerivedFunctorAt`, which supplies the pointwise computation input
    required by the Chapter `13` existence bridge.
- primitive data: the functor `F` and, for each cochain complex `K`, a quasi-isomorphism
  `K ⟶ I` to a K-injective complex `I`;
- derived API: first pointwise right-derived existence for `F`, obtained from the K-injective
  replacements via `kInjective_computesRightDerivedFunctorAt` and
  `Functor.hasPointwiseRightDerivedFunctor_of_exists_computesRightDerivedAt`, and then global
  right-derived existence via
  `Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor`.

This file should therefore keep only the global existence statement as its source-facing API and
reuse the existing owner path for K-injective computation, pointwise existence, and global
existence, rather than rebuilding the costructured-arrow localization argument locally.
-/ 
/-- Lemma 13.31.7: if every cochain complex in an abelian category admits a quasi-isomorphism to
a K-injective complex, then any functor `K(\mathcal A) ⥤ \mathcal D'` has a right derived
functor with respect to quasi-isomorphisms. The statement is organized around the canonical owner
predicates `Functor.HasPointwiseRightDerivedFunctor` and `Functor.HasRightDerivedFunctor`, with the
K-injective replacement hypothesis supplying the source-facing existence data. -/
theorem hasRightDerivedFunctor_of_kInjective_resolutions
    (F : KHom ⥤ 𝒟')
    (hKI :
      ∀ K : CochainComplex 𝒜 ℤ,
        ∃ (I : CochainComplex 𝒜 ℤ) (_ : I.IsKInjective) (s : K ⟶ I), QuasiIso s) :
    F.HasRightDerivedFunctor W := sorry

end

end CategoryTheory
