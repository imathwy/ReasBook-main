import StacksProject_2024.Chap20.Lemma_20_47_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open DerivedCategory.TStructure

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/- Domain-style sampling for Lemma 20.47.8:
- primary domain: local bounded-above derived `𝒪_X`-modules and pseudo-coherence from
  pseudo-coherent cohomology sheaves;
- sampled owner declarations:
  `ModuleDerived`,
  `ModuleDerived.IsLocallyBoundedAbove`,
  `moduleRestrictionToOpenDerived`,
  `DerivedCategory.IsLE`,
  `DerivedCategory.homologyFunctor`,
  `CategoryTheory.boundedAbove_isMPseudoCoherent_of_homology`;
- best owner abstraction: the core derived object owner is `ModuleDerived X`, local restriction is
  owned by `moduleRestrictionToOpenDerived X`, cohomological bounded-above-ness is expressed by the
  canonical predicates `IsLE n`, the source-facing local bounded-above hypothesis is the owner
  `ModuleDerived.IsLocallyBoundedAbove`, and the cohomology-sheaf input is owned by
  `((H^i).obj E).IsMPseudoCoherent (m - i)`, and the affine bounded-above pseudo-coherence input is the
  Chapter 15 theorem `boundedAbove_isMPseudoCoherent_of_homology`;
- primitive data: a derived object `E`, neighborhoodwise upper cohomological bounds after
  restriction to opens as `E.IsLocallyBoundedAbove`, and the pseudo-coherence hypotheses on the
  cohomology sheaves;
- derived API: the source-facing local bounded-above predicate and the derived pseudo-coherence
  conclusion.

Source/core/bridge triage:
- `source-facing`: `isMPseudoCoherent_of_isLocallyBoundedAbove_of_homology`;
- `core/canonical`: `ModuleDerived`, `moduleRestrictionToOpenDerived`, `IsLE`,
  and `boundedAbove_isMPseudoCoherent_of_homology`;
- `bridge/view`: local restriction from `D(𝒪_X)` to `D(𝒪_U)`. -/

local notation "ModX" => RingedSpace.Modules X
local notation "DModX" => ModuleDerived X
local notation:max "H^" i:max => DerivedCategory.homologyFunctor ModX i

-- Proof sketch: work locally near each point. On a neighborhood where `E` becomes bounded above,
-- apply the bounded-above algebraic argument of Lemma `15.65.10` to the restricted object, using
-- the hypotheses on the cohomology sheaves `H^i(E)`. This yields local `m`-pseudo-coherence of
-- the restriction, and Lemma `20.47.2` upgrades the local strictly perfect approximations to
-- `IsMPseudoCoherent E m`.
/-- Lemma 20.47.8: if `E` is locally bounded above and every cohomology sheaf `H^i(E)` is
`(m - i)`-pseudo-coherent, then `E` is `m`-pseudo-coherent. This local formulation covers the
parenthetical bounded-above case as a special case. -/
@[stacks 09V8]
theorem isMPseudoCoherent_of_isLocallyBoundedAbove_of_homology
    (E : DModX) (m : ℤ)
    (hbounded : E.IsLocallyBoundedAbove)
    (hH :
      ∀ i : ℤ, ((H^i).obj E).IsMPseudoCoherent (m - i)) :
    E.IsMPseudoCoherent m := sorry

/-- Canonical bounded-above companion to Lemma 20.47.8: a global bound `E.IsLE n` gives the
special case mentioned in the source by upgrading `E` to the source-facing local bounded-above
owner `E.IsLocallyBoundedAbove`. -/
theorem isMPseudoCoherent_of_isLE_of_homology
    (E : DModX) (m n : ℤ)
    (hLE : E.IsLE n)
    (hH : ∀ i : ℤ, ((H^i).obj E).IsMPseudoCoherent (m - i)) :
    E.IsMPseudoCoherent m := by
  have hbounded : E.IsLocallyBoundedAbove := by
    intro x
    refine ⟨⊤, by simp, n, ?_⟩
    sorry
  exact isMPseudoCoherent_of_isLocallyBoundedAbove_of_homology E m hbounded hH

end AlgebraicGeometry.RingedSpace.ModuleDerived
