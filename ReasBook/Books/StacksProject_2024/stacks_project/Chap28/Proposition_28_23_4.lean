import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X : Scheme.{u}}

-- Semantic recall: `lean_leansearch` surfaced the scheme-module quasi-coherence owner
-- `SheafOfModules.IsQuasicoherent`; the categorical surface here is the full subcategory attached
-- to the canonical object property `SheafOfModules.isQuasicoherent X.ringCatSheaf`, with inclusion
-- `ObjectProperty.ι` and right-adjoint ownership recorded by `Functor.IsLeftAdjoint`.

/-- The canonical object property of quasi-coherent `\mathcal O_X`-modules on a scheme `X`. -/
@[stacks 077P]
abbrev isQuasiCoherentModule (X : Scheme.{u}) : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

/-- The full subcategory `\mathit{QCoh}(\mathcal O_X)` of quasi-coherent `\mathcal O_X`-modules
on a scheme `X`. -/
@[stacks 077P]
abbrev QCoh (X : Scheme.{u}) := (isQuasiCoherentModule X).FullSubcategory

/-- The inclusion functor `\mathit{QCoh}(\mathcal O_X) \to \operatorname{Mod}(\mathcal O_X)`. -/
@[stacks 077P]
abbrev qcohInclusion (X : Scheme.{u}) : QCoh X ⥤ X.Modules :=
  (isQuasiCoherentModule X).ι

/-- Companion abelian-category instance for Proposition 28.23.4: the category
`\mathit{QCoh}(\mathcal O_X)` is abelian. -/
@[stacks 077P, instance]
instance quasiCoherentModules_abelian (X : Scheme.{u}) :
    Abelian (QCoh X) := sorry

/-- Proposition 28.23.4 (1): for a scheme `X`, the category `\mathit{QCoh}(\mathcal O_X)` of
quasi-coherent `\mathcal O_X`-modules is a Grothendieck abelian category. -/
@[stacks 077P]
theorem quasiCoherentModules_isGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian (QCoh X) := sorry

/-- Proposition 28.23.4 (2): consequently, the category `\mathit{QCoh}(\mathcal O_X)` has enough
injectives. -/
@[stacks 077P]
theorem quasiCoherentModules_enoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (QCoh X) := sorry

/-- Proposition 28.23.4 (3): consequently, the category `\mathit{QCoh}(\mathcal O_X)` has all
limits. -/
@[stacks 077P]
theorem quasiCoherentModules_hasLimits (X : Scheme.{u}) :
    HasLimits (QCoh X) := sorry

/-- Proposition 28.23.4 (4): the inclusion functor
`\mathit{QCoh}(\mathcal O_X) \to \operatorname{Mod}(\mathcal O_X)` has a right adjoint. In the
canonical owner form, this is recorded by saying that the inclusion functor is a left adjoint. -/
@[stacks 077P]
theorem quasiCoherentInclusion_isLeftAdjoint (X : Scheme.{u}) :
    Functor.IsLeftAdjoint (qcohInclusion X) := sorry

/-- Proposition 28.23.4 (5): for every quasi-coherent `\mathcal O_X`-module, the counit of the
adjunction between the inclusion `\mathit{QCoh}(\mathcal O_X) \to \operatorname{Mod}(\mathcal O_X)`
and its right adjoint is an isomorphism. -/
@[stacks 077P]
theorem quasiCoherentInclusion_counit_app_isIso (X : Scheme.{u})
    [Functor.IsLeftAdjoint (qcohInclusion X)] (ℱ : QCoh X) :
    IsIso ((Adjunction.ofIsLeftAdjoint (qcohInclusion X)).counit.app
      ((qcohInclusion X).obj ℱ)) := sorry

end

end AlgebraicGeometry
