import Mathlib
import stacks_project.Chap13.Lemma_13_31_9
import stacks_project.Chap17.Definition_17_5_1
import stacks_project.Chap17.Lemma_17_20_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.32.9:
- primary domain: K-injective cochain complexes of module sheaves on ringed spaces under the
  pullback-pushforward adjunction attached to a flat morphism;
- sampled owner declarations:
  `RingedSpace.Hom.IsFlat`,
  `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`,
  `SheafOfModules.pullbackPushforwardAdjunction`,
  `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- best owner abstraction: the Chapter 13 owner theorem for a right adjoint to an exact additive
  left adjoint, specialized to `f^* ⊣ f_*` for a flat morphism of ringed spaces.

Primitive-vs-derived split:
- primitive data: a morphism `f : X ⟶ Y`, the canonical owner hypothesis `[RingedSpace.Hom.IsFlat f]`,
  and a K-injective complex `I : CochainComplex (RingedSpace.Modules X) ℤ`;
- derived API: K-injectivity of the pushforward complex `((f _*).mapHomologicalComplex (up ℤ)).obj I`.

Source/core/bridge triage:
- `source-facing`: a flat direct image on ringed spaces sends K-injective complexes to
  K-injective complexes;
- `core/canonical`: `CategoryTheory.right_adjoint_preserves_isKInjective_of_exact_left_adjoint`;
- `bridge/view`: this file is the ringed-space specialization using the canonical owners
  `RingedSpace.Hom.IsFlat`, `AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact`, and
  `f _*`.
-/

section

variable {X Y : RingedSpace.{u}}

local notation "ModX" => (RingedSpace.Modules X)
local notation "ModY" => (RingedSpace.Modules Y)

-- Proof sketch: the adjunction `f^* ⊣ f_*` is the canonical module-sheaf adjunction from Chapter
-- 6, and flatness upgrades `f^*` to an exact functor by Lemma `17.20.2`. Apply the Chapter 13
-- owner theorem saying that a right adjoint to an exact additive left adjoint preserves
-- K-injective cochain complexes.
/-- Lemma 20.32.9: for a flat morphism of ringed spaces `f : X ⟶ Y`, the direct image of a
K-injective complex of `\mathcal O_X`-modules is K-injective as a complex of
`\mathcal O_Y`-modules. -/
theorem ringedSpaceModulePushforward_isKInjective_of_flat
    (f : X ⟶ Y) [RingedSpace.Hom.IsFlat f]
    (I : CochainComplex ModX ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective (((f _*).mapHomologicalComplex (up ℤ)).obj I) := by
  let adj :=
    SheafOfModules.pullbackPushforwardAdjunction (RingedSpace.Hom.toRingCatSheafHom f)
  let hExact := AlgebraicGeometry.RingedSpace.Hom.IsFlat.pullback_exact f
  letI : CategoryTheory.Limits.PreservesFiniteLimits (f^*) :=
    (CategoryTheory.exactFunctor_iff (f^*)).mp hExact |>.1
  letI : CategoryTheory.Limits.PreservesBinaryBiproducts (f^*) :=
    CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts (f^*)
  letI : (f^*).Additive := Functor.additive_of_preservesBinaryBiproducts _
  letI : (f _*).Additive := adj.right_adjoint_additive
  simpa using
    right_adjoint_preserves_isKInjective_of_exact_left_adjoint
      (f _*) (f^*) adj hExact I

end

end AlgebraicGeometry.RingedSpace
