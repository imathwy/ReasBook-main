import StacksProject_2024.Chap17.Definition_17_12_1

open AlgebraicGeometry
open CategoryTheory
open Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The affine-open section submodule cut out by a subsheaf `\mathcal G \subset \mathcal F`. -/
def affineOpenSubsheafSectionsSubmodule
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : X.affineOpens) :
    Submodule Γ(X, U.1) (ℱ.val.obj (op U.1)) :=
  LinearMap.range ((𝒢.arrow.val.app (op U.1)).hom)

/-- Unfold the affine-open section submodule cut out by a subsheaf. -/
theorem affineOpenSubsheafSectionsSubmodule_def
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : X.affineOpens) :
    affineOpenSubsheafSectionsSubmodule 𝒢 U =
      LinearMap.range ((𝒢.arrow.val.app (op U.1)).hom) :=
  rfl

/-- Membership in the affine-open section submodule cut out by a subsheaf. -/
theorem mem_affineOpenSubsheafSectionsSubmodule
    {ℱ : X.Modules} (𝒢 : Subobject ℱ) (U : X.affineOpens)
    {x : Γ(ℱ, U.1)} :
    x ∈ affineOpenSubsheafSectionsSubmodule 𝒢 U ↔
      ∃ y : Γ((𝒢 : X.Modules), U.1), ((𝒢.arrow.val.app (op U.1)).hom) y = x := by
  rfl

end AlgebraicGeometry.Scheme.Modules
