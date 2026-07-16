import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme} [MonoidalCategory X.Modules]

/- Semantic recall: `lean_leansearch` surfaced the canonical quasi-affine owner
`Scheme.IsQuasiAffine` and the affine-open owner `IsAffineOpen`. Local Chapter 28 API represents
invertible modules by `Functor.IsEquivalence (tensorRight L)`. The local packaged owner
`Scheme.Modules.Invertible.sectionNonvanishingOpen` currently imports a universe-monomorphic
Chapter 17 file that fails during item-file checking, so this file records the same source-facing
`X_s` as the explicit stalkwise nonvanishing set below. -/

/-- The stalkwise nonvanishing locus `X_s` of a global section of an invertible
`\mathcal O_X`-module, written explicitly to avoid depending on the currently unavailable
packaged nonvanishing-open owner. -/
def sectionNonvanishingSet (L : X.Modules) (s : Γ(L, ⊤)) : Set X :=
  {x | ((TopCat.Presheaf.Γgerm L.val.presheaf x).hom s) ∉
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.stalkModuleCat L x)))}

/-- Membership in `sectionNonvanishingSet` is exactly stalkwise nonvanishing modulo the maximal
ideal of the local ring. -/
theorem mem_sectionNonvanishingSet
    {L : X.Modules} {s : Γ(L, ⊤)} {x : X} :
    x ∈ sectionNonvanishingSet L s ↔
      ((TopCat.Presheaf.Γgerm L.val.presheaf x).hom s) ∉
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (RingedSpace.stalkModuleCat L x))) := sorry

/-- A section cuts out an affine nonvanishing open between a finite set and an ambient open. -/
structure SectionAffineNonvanishingOpenBetween
    (L : X.Modules) (s : Γ(L, ⊤)) (U : X.Opens) (E : Set X) (W : X.Opens) :
    Prop where
  nonvanishing_eq : (U : Set X) = sectionNonvanishingSet L s
  isAffineOpen : IsAffineOpen U
  subset_open : E ⊆ (U : Set X)
  le_open : U ≤ W

/-- Lemma 28.29.7: on a quasi-affine scheme, for an invertible `\mathcal O_X`-module `L`,
every finite subset `E` contained in an open `W` is contained in an affine nonvanishing open
`X_s` of a global section of `L`, and this nonvanishing open is contained in `W`. -/
@[stacks 0F20]
theorem exists_section_affine_nonvanishingOpen_between_finiteSet_and_open_of_isQuasiAffine
    (hX : X.IsQuasiAffine) (L : X.Modules) [hL : Functor.IsEquivalence (tensorRight L)]
    (E : Set X) (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ (W : Set X)) :
    ∃ s : Γ(L, ⊤), ∃ U : X.Opens,
      SectionAffineNonvanishingOpenBetween L s U E W := sorry

end AlgebraicGeometry.Scheme.Modules
