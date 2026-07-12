import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the existing owners
-- `SheafOfModules.IsQuasicoherent`, `AlgebraicGeometry.IsAffineOpen`, `Scheme.Modules`, and
-- `Module.Projective`. The Stacks notion is therefore best represented as the affine-open
-- sectionwise projectivity property on scheme modules; quasi-coherence remains an ambient source
-- hypothesis in later results, but it is not part of this owner itself.

/-- Definition 28.21.1: a quasi-coherent `\mathcal{O}_X`-module `ℱ` is locally projective if for
every affine open `U ⊆ X`, the `Γ(X, U)`-module `Γ(ℱ, U)` is projective. -/
class IsLocallyProjective (ℱ : X.Modules) : Prop where
  /-- Affine sections of a locally projective module are projective over the ring of functions on
  that affine open. -/
  out : ∀ U : X.affineOpens, Module.Projective Γ(X, U) Γ(ℱ, U)

/-- A locally projective module has projective sections on every affine open. -/
theorem IsLocallyProjective.projective_sections
    (ℱ : X.Modules) [hℱ : IsLocallyProjective ℱ]
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Projective Γ(X, U) Γ(ℱ, U) := by
  exact hℱ.out ⟨U, hU⟩

/-- A locally projective module has projective sections on every affine open,
packaged as an element of `X.affineOpens`. -/
theorem IsLocallyProjective.projective_sections_affineOpen
    (ℱ : X.Modules) [hℱ : IsLocallyProjective ℱ]
    (U : X.affineOpens) :
    Module.Projective Γ(X, U) Γ(ℱ, U) :=
  hℱ.out U

/-- On an affine open, sections of a locally projective module form a projective
module over the ring of functions on that open. -/
instance instProjectiveSectionsOfIsLocallyProjective
    (ℱ : X.Modules) [hℱ : IsLocallyProjective ℱ]
    (U : X.Opens) [hU : Fact (IsAffineOpen U)] :
    Module.Projective Γ(X, U) Γ(ℱ, U) :=
  IsLocallyProjective.projective_sections ℱ U hU.out

/-- Local projectivity is exactly affine-open sectionwise projectivity. -/
theorem isLocallyProjective_iff
    (ℱ : X.Modules) :
    IsLocallyProjective ℱ ↔
      ∀ U : X.Opens, IsAffineOpen U → Module.Projective Γ(X, U) Γ(ℱ, U) := by
  constructor
  · intro hℱ U hU
    exact IsLocallyProjective.projective_sections ℱ U hU
  · intro hℱ
    exact ⟨fun U ↦ hℱ U.1 U.2⟩

end AlgebraicGeometry.Scheme.Modules
