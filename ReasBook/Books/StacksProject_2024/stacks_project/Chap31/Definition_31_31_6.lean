import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X P : Scheme.{u}} {ℰ : X.Modules}

/-- A quotient of `ℰ` by an invertible `\mathcal O_X`-module. -/
structure ProjectiveBundleQuotient
    (ℰ : X.Modules) [MonoidalCategory X.Modules] where
  /-- The invertible quotient module. -/
  module : X.Modules
  /-- The quotient module is invertible. -/
  isInvertible : Functor.IsEquivalence (tensorRight module)
  /-- The quotient map `ℰ ⟶ \mathcal L`. -/
  hom : ℰ ⟶ module
  /-- The quotient map is surjective, encoded as an epimorphism in `X.Modules`. -/
  hom_epi : Epi hom

/-- The target of a projective-bundle quotient is invertible. -/
instance projectiveBundleQuotient_isInvertible
    [MonoidalCategory X.Modules] (q : ProjectiveBundleQuotient ℰ) :
    Functor.IsEquivalence (tensorRight q.module) :=
  q.isInvertible

/-- The morphism underlying a projective-bundle quotient is an epimorphism. -/
instance projectiveBundleQuotient_hom_epi
    [MonoidalCategory X.Modules] (q : ProjectiveBundleQuotient ℰ) :
    Epi q.hom :=
  q.hom_epi

/-- A lift of `f : T ⟶ X` through `π : P ⟶ X`, i.e. a section of `π` over the base `f`. -/
abbrev ProjectiveBundleLifts {T : Scheme.{u}} (π : P ⟶ X) (f : T ⟶ X) :=
  { σ : T ⟶ P // σ ≫ π = f }

/-- A morphism `π : P ⟶ X` is a projective bundle associated to `ℰ` if its `T`-valued points over
`X` represent invertible quotients of the pullback of `ℰ` to `T`. -/
class IsProjectiveBundle (π : P ⟶ X) (ℰ : outParam X.Modules) where
  /-- The universal quotient description of `π`. -/
  liftEquiv :
    ∀ ⦃T : Scheme.{u}⦄ [MonoidalCategory T.Modules] (f : T ⟶ X),
      ProjectiveBundleLifts π f ≃
        ProjectiveBundleQuotient ((Scheme.Modules.pullback f).obj ℰ)
  /-- A projective bundle morphism is separated. -/
  separated : IsSeparated π

/-- A projective bundle is separated over its base. -/
instance isSeparated_of_isProjectiveBundle
    {π : P ⟶ X} [h : IsProjectiveBundle π ℰ] :
    IsSeparated π :=
  h.separated

/-- The quotient correspondence for a projective bundle after arbitrary base change. -/
noncomputable abbrev projectiveBundleLiftEquivQuotient
    {π : P ⟶ X} [IsProjectiveBundle π ℰ]
    {T : Scheme.{u}} [MonoidalCategory T.Modules] (f : T ⟶ X) :
    ProjectiveBundleLifts π f ≃
      ProjectiveBundleQuotient ((Scheme.Modules.pullback f).obj ℰ) :=
  (inferInstance : IsProjectiveBundle π ℰ).liftEquiv f

end AlgebraicGeometry.Scheme
