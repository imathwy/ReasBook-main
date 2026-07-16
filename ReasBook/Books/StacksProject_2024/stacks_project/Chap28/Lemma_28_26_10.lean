import StacksProject_2024.stacks_project.Chap28.Lemma_28_26_9
import StacksProject_2024.stacks_project.Chap28.Lemma_28_26_4
import StacksProject_2024.stacks_project.Chap28.Lemma_28_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "IsInvertibleX" =>
  (fun ℒ : ModX ↦ Functor.IsEquivalence (CategoryTheory.MonoidalCategory.tensorRight ℒ))

-- Semantic recall: `lean_leansearch` surfaced the canonical morphism-property owners
-- `QuasiCompact` and `IsDominant`, and the generic mathlib `Proj.fromOfGlobalSections` layer.
-- Nearby project files verify the dependency-closed graded-global-sections owner `Γ_*(ℒ)` and
-- record Lemma 28.26.9 as a recall block because the specialized canonical morphism
-- `X ⟶ Proj(Γ_*(X, ℒ))` from an invertible sheaf is not yet packaged as concrete API.  This item
-- therefore records the exact source-facing theorem as a labeled recall block, rather than
-- introducing a fake theorem over an arbitrary replacement morphism or a noncanonical `Proj` input.

/- Lemma 28.26.10: let `X` be a scheme and let `\mathcal L` be an invertible
`\mathcal O_X`-module. Set `S = Γ_*(X, \mathcal L)`. Assume that every point of `X` lies in one
of the nonvanishing opens `X_s`, for some positive homogeneous `s ∈ S_+`, and assume that `X` is
quasi-compact. Then the canonical morphism
`f : X ⟶ Proj(S)` of Lemma 28.26.9 is quasi-compact and has dense image.

The currently available dependency-closed API exposes the graded section ring, the generic
`Proj.fromOfGlobalSections` construction and its basic-open preimage theorem, and the canonical
scheme-morphism properties `QuasiCompact` and `IsDominant`. The exact specialized canonical
morphism of Lemma 28.26.9, together with its source-facing `X_s` compatibility for all positive
homogeneous sections of `Γ_*(X, \mathcal L)`, is not yet a concrete declaration in this local API,
so the conclusion is recorded here without inventing a parallel wrapper. -/
#check (fun {X Y : Scheme} (f : X ⟶ Y) ↦ QuasiCompact f)
#check (fun {X Y : Scheme} (f : X ⟶ Y) ↦ IsDominant f)
#check (fun (X : Scheme.{u}) ↦ CompactSpace X)
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.basicOpen
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
#check AlgebraicGeometry.Γ_restrict_isLocalization
#check fun {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (f : Γ(X, ⊤)) ↦
  (inferInstance :
    IsLocalizedModule (.powers f)
      (ModuleCat.Hom.hom (ℱ.val.map (CategoryTheory.homOfLE (X.basicOpen_le f)).op)))

end AlgebraicGeometry.Scheme.Modules
