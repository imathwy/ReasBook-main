import StacksProject_2024.Chap20.«20_2_0_4»
import StacksProject_2024.Chap20.Open_subspace_module_core

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open RingedSpace.Hom
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.7.4:
- primary domain: higher direct images of sheaves of modules on ringed spaces and their behavior
  under restriction to an open subspace;
- sampled owner declarations:
  `higherDirectImageModule`,
  `moduleRestrictionToOpen`,
  `restrictedMorphismToOpen`,
  `openSubspaceModuleCategory`,
  `preimageOpen`;
- best owner abstraction: the source-facing degree-`p` comparison here is a specialization of the
  later Chapter 20 derived restriction comparison; the source-facing higher direct image terms
  should therefore reuse the Chapter 20 owner `higherDirectImageModule`, while the restriction
  terms should be written through the intrinsic open-subspace restriction owner
  `moduleRestrictionToOpen X U`, and the restricted morphism should be taken directly from the
  open-subspace owner `restrictedMorphismToOpen`;
- primitive data: a morphism of ringed spaces `f : X ⟶ Y`, an open subset `V ⊆ Y`, the canonical
  restricted morphism `restrictedMorphismToOpen f V`, and a module sheaf `ℱ : X.Modules`;
- derived API: the restriction owner terms
  `(moduleRestrictionToOpen Y V).obj (R^{p}_[f](ℱ))` and
  `(moduleRestrictionToOpen X (preimageOpen f V)).obj ℱ`, together with the restricted higher
  direct image `R^{p}_[restrictedMorphismToOpen f V]
    ((moduleRestrictionToOpen X (preimageOpen f V)).obj ℱ)`.

Source/core/bridge triage:
- `source-facing`: the degree-`p` higher-direct-image restriction statement of Lemma 20.7.4;
- `core/canonical`: `higherDirectImageModule`, `moduleRestrictionToOpen`,
  `restrictedMorphismToOpen`, and `openSubspaceModuleCategory`;
- `bridge/view`: the later derived-category restriction comparison together with the passage from
  that derived statement to the degree-`p` higher-direct-image statement.
-/

variable {X Y : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y)

variable [hfAdd : (f _*).Additive]
variable [hfRes : HasInjectiveResolutions (RingedSpace.Modules X)]

section

variable (V : Opens Y.carrier)
variable [hAdd : ((restrictedMorphismToOpen f V) _*).Additive]
variable [hRes : HasInjectiveResolutions (openSubspaceModuleCategory X (preimageOpen f V))]

local notation "U" => preimageOpen f V
local notation "g" => restrictedMorphismToOpen f V
local notation3:max "Rf^{" i:arg "}" "(" F ")" =>
  @higherDirectImageModule X Y f hfAdd hfRes F i
local notation3:max "Rg^{" i:arg "}" "(" F ")" =>
  @higherDirectImageModule
    (X.restrict (preimageOpen f V).isOpenEmbedding) (Y.restrict V.isOpenEmbedding)
    (restrictedMorphismToOpen f V) hAdd hRes F i

/-- Lemma 20.7.4: let `U := preimageOpen f V` and `g := restrictedMorphismToOpen f V`. Then
the restriction of `R^{p}_[f](ℱ)` to `V` is canonically isomorphic to
`R^{p}_[g]((moduleRestrictionToOpen X U).obj ℱ)`. -/
-- Proof sketch: use the Chapter 20 objectwise derived restriction theorem
-- for the derived object attached to `ℱ`, then read off the degree-`p` higher-direct-image
-- comparison. The restriction terms are written through the Chapter 20 open-subspace owner
-- `moduleRestrictionToOpen`, and the higher direct images are written through the Chapter 20
-- owner notation `R^{p}_[f](ℱ)`.
@[stacks 01E5]
theorem higherDirectImageModule_restrict_isomorphic
    (p : ℕ) (ℱ : RingedSpace.Modules X) :
    IsIsomorphic
      ((moduleRestrictionToOpen Y V).obj (Rf^{p}(ℱ)))
      (Rg^{p}((moduleRestrictionToOpen X U).obj ℱ)) := by
  sorry

end

end AlgebraicGeometry.RingedSpace
