import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape

universe v₁ v₂ u₁ u₂

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {𝒟' : Type u₂}
  [Category.{v₁} 𝒜] [Abelian 𝒜]
  [Category.{v₂} 𝒟']

/- Domain-style sampling for Lemma 13.31.6:
- primary domain: pointwise right derived functors on the homotopy category `K(\mathcal A)`,
  computed on K-injective complexes and transported along quasi-isomorphisms;
- sampled owner declarations:
  `Functor.ComputesRightDerivedAt`,
  `Functor.HasPointwiseRightDerivedFunctorAt`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `DerivedCategory.Qh`,
  `CochainComplex.IsKInjective.Qh_map_bijective`;
- best owner abstractions:
  `source-facing`: the statement that a K-injective complex computes the right derived functor;
  `core/canonical`: `Functor.ComputesRightDerivedAt` and the transport owner
    `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`;
  `bridge/view`: the downstream use of the canonical transport theorem for objects
    quasi-isomorphic to a K-injective one.
- primitive data: the functor `F` and the K-injective complex `I`.
- derived API: downstream pointwise-definedness statements are obtained by transporting the
  computation theorem at `(HomotopyCategory.quotient 𝒜 (up ℤ)).obj I` along a quasi-isomorphism
  using `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`.

The main owner-level theorem here is therefore the computation statement at a K-injective object.
The pointwise-existence statement for an arbitrary quasi-isomorphic object should therefore be
handled downstream by the canonical transport API, not by a separate local wrapper theorem.
-/

variable (F : HomotopyCategory 𝒜 (up ℤ) ⥤ 𝒟')

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)
local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)

-- Proof sketch: `IsKInjective.Qh_map_bijective` says every arrow into a K-injective complex is
-- uniquely determined by its image in the derived category. Applied to the costructured-arrow
-- category over `DerivedCategory.Qh.obj ((KQ).obj I)`, this makes the identity denominator
-- terminal, so the
-- pointwise right derived value is just `F.obj ((KQ).obj I)` and the canonical unit is an
-- isomorphism.
/-- Lemma 13.31.6: every K-injective complex computes the right derived functor of
`F : K(\mathcal A) ⥤ \mathcal D'` with respect to quasi-isomorphisms. -/
theorem kInjective_computesRightDerivedFunctorAt
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    F.ComputesRightDerivedAt Qis ((KQ).obj I) := by
  sorry

end

end CategoryTheory
