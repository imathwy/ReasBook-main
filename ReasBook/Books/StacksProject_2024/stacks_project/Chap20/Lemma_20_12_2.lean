import StacksProject_2024.Chap20.Lemma_20_8_1
import StacksProject_2024.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.12.2:
- primary domain: sheaves of modules on a ringed space, viewed through their underlying abelian
  sheaves and the flasqueness predicate;
- sampled owner declarations:
  `(RingedSpace.ringCatSheaf X)`,
  `(RingedSpace.Modules X)`,
  `moduleUnderlyingSheaf`,
  `TopCat.Sheaf.IsFlasque`;
- best owner abstraction: the Chapter 20 ringed-space owner `(RingedSpace.Modules X)`, with
  `moduleUnderlyingSheaf` as the canonical bridge to the flasque sheaf statement;
- primitive data: a ringed space `X`, an object `ℐ : (RingedSpace.Modules X)`, and the categorical
  injectivity hypothesis `Injective ℐ`;
- derived API: flasqueness of the underlying abelian sheaf.

Source/core/bridge triage:
- `source-facing`: the statement that injective `𝒪_X`-modules are flasque;
- `core/canonical`: `(RingedSpace.Modules X)` and `TopCat.Sheaf.IsFlasque`;
- `bridge/view`: `moduleUnderlyingSheaf`.

This file should therefore reuse the earlier Chapter 20 owner declarations rather than duplicate a
local `ringedSpaceRingCatSheaf` abbreviation. -/

-- Proof sketch: by the flasqueness owner API from Definition `20.12.1`, it suffices to show that
-- every restriction morphism of the underlying additive sheaf is epi. For `AddCommGrpCat` this is
-- equivalent to surjectivity, and the companion API from Lemma `20.8.1` supplies that
-- surjectivity for injective `𝒪_X`-modules.

/-- Lemma 20.12.2: for a ringed space `(X, 𝒪_X)`, any injective `𝒪_X`-module
is flasque as a sheaf of abelian groups. -/
@[stacks 09SX]
theorem module_isFlasque_of_injective
    (ℐ : X.Modules) (hℐ : Injective ℐ) :
    TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℐ) := by
  -- Check flasqueness by showing every restriction map of the underlying additive sheaf is epi.
  refine ⟨fun {U V} i ↦ (AddCommGrpCat.epi_iff_surjective _).2 ?_⟩
  -- The categorical inclusion `i` is equivalent to an inclusion of opens via `leOfHom i.unop`.
  simpa using
    underlying_module_sections_restriction_surjective_of_injective ℐ hℐ (leOfHom i.unop)

/-- Typeclass form of Lemma 20.12.2: the underlying additive sheaf of an injective `𝒪_X`-module
is flasque. -/
instance instModuleUnderlyingSheafIsFlasqueOfInjective
    (ℐ : X.Modules) [hℐ : Fact (Injective ℐ)] :
    TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℐ) :=
  module_isFlasque_of_injective ℐ hℐ.out

end AlgebraicGeometry.RingedSpace
