import StacksProject_2024.stacks_project.Chap28.Lemma_28_26_10
import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1

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

-- Semantic recall: `lean_leansearch` surfaced the canonical owners
-- `AlgebraicGeometry.Proj.fromOfGlobalSections`, `AlgebraicGeometry.IsOpenImmersion`, and
-- `AlgebraicGeometry.IsDominant`.  The local dependencies record Lemmas 28.26.9 and 28.26.10 as
-- source-faithful recall blocks because the specialized canonical morphism
-- `X ⟶ Proj(Γ_*(X, ℒ))` associated to an invertible sheaf is not yet packaged as concrete API.
-- This item therefore records the exact source-facing theorem without inventing a parallel
-- wrapper over an arbitrary morphism.

/- Lemma 28.26.11: let `X` be a scheme and let `\mathcal L` be an invertible
`\mathcal O_X`-module. Set `S = Γ_*(X, \mathcal L)`. If `\mathcal L` is ample, then the
canonical morphism `f : X ⟶ Proj(S)` of Lemma 28.26.9 is an open immersion with dense image.

The dependency-closed API currently exposes the graded global-section ring, the generic projective
spectrum and global-sections morphism, the open-immersion property, and the dominant/dense-image
property. The exact specialized morphism of Lemma 28.26.9 is not yet a concrete declaration in the
local API, so this label is kept as a recall block rather than a theorem over a noncanonical
replacement map. -/
#check AlgebraicGeometry.RingedSpace.gradedGlobalSections
#check AlgebraicGeometry.RingedSpace.gradedGlobalSectionsDegree
#check AlgebraicGeometry.Proj
#check AlgebraicGeometry.Proj.fromOfGlobalSections
#check AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen
#check (fun {Y : Scheme} (f : X ⟶ Y) ↦ IsOpenImmersion f)
#check (fun {Y : Scheme} (f : X ⟶ Y) ↦ IsDominant f)
#check (fun (ℒ : ModX) [Invertible ℒ] ↦ IsAmple ℒ)

end AlgebraicGeometry.Scheme.Modules
