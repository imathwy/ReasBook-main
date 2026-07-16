import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap20.Definition_20_47_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

open _root_.AlgebraicGeometry.RingedSpace.ModuleDerived

/- Domain-style sampling for Lemma 20.47.2:
- primary domain: pseudo-coherence for derived `𝒪_X`-modules and the induced
  pseudo-coherence of any chosen representing cochain complex;
- sampled owner declarations:
  `ModuleDerived`,
  `IsMPseudoCoherent`,
  `isMPseudoCoherent_iff_exists_mPseudoCoherent_representative`,
  `ModuleDerived.IsMPseudoCoherent.of_representation`;
- best owner abstraction: the intrinsic Chapter 20 owner
  `ModuleDerived.IsMPseudoCoherent` from `Definition_20_47_1`; the canonical bridge is that
  owner applied to the represented object `Q.obj K`, while the textbook formulation with an
  arbitrary chosen representative is the source-facing owner-level companion
  `ModuleDerived.IsMPseudoCoherent.of_representation`;
- primitive data: the representative complex `K` and the owner witness
  `IsMPseudoCoherent (DerivedCategory.Q.obj K) m`;
- derived API: the source-facing representative bridge
  `ModuleDerived.IsMPseudoCoherent.of_representation`.

Source/core/bridge triage:
- `source-facing`: the corollary below about a chosen representing complex;
- `core/canonical`: `ModuleDerived X`, `IsMPseudoCoherent`, and `DerivedCategory.Q`;
- `bridge/view`: reuse of the intrinsic owner predicate from `Q.obj K` across an
  isomorphism `DerivedCategory.Q.obj K ≅ E`. -/
local notation "DModX" => ModuleDerived X

/- Lemma 20.47.2 (1): the intrinsic owner is the Chapter 20 predicate
`ModuleDerived.IsMPseudoCoherent`, and
`isMPseudoCoherent_iff_exists_openCover` is its open-cover bridge. -/
recall IsMPseudoCoherent

-- Proof sketch: choose an `m`-pseudo-coherent representative `L` of `E`, transport that
-- representative witness across the chosen isomorphism `e : DerivedCategory.Q.obj K ≅ E`, and
-- then use Lemma `20.46.8` to realize the resulting local derived maps on `Q.obj K` by actual
-- morphisms of restricted complexes for `K`. Those local morphisms satisfy the complex-level
-- approximation criterion, so `K` is `m`-pseudo-coherent.
namespace ModuleDerived

/-- Lemma 20.47.2 (2): if a derived `𝒪_X`-module is `m`-pseudo-coherent, then every
cochain complex representing it is `m`-pseudo-coherent. -/
@[stacks 08CC]
theorem IsMPseudoCoherent.of_representation
    {E : DModX} {m : ℤ} {K : CochainComplex (RingedSpace.Modules X) ℤ}
    (hE : E.IsMPseudoCoherent m) (e : DerivedCategory.Q.obj K ≅ E) :
    CochainComplex.IsMPseudoCoherent K m := by
  rcases hE with ⟨L, eL, hL⟩
  have hK : IsMPseudoCoherent (DerivedCategory.Q.obj K) m := by
    exact ⟨L, e ≪≫ eL, hL⟩
  sorry

end ModuleDerived

end AlgebraicGeometry.RingedSpace
