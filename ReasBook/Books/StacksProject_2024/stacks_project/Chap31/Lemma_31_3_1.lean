import Mathlib
import StacksProject_2024.stacks_project.Chap06.Definition_6_26_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_25_2
import StacksProject_2024.stacks_project.Chap31.Definition_31_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (ℱ : X.Modules) (𝒢 : S.Modules)
variable [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
variable [MonoidalCategory X.Modules]

local notation "ModX" => X.Modules
local notation:max f:max "^*" => Scheme.Modules.pullback f

-- Semantic recall: `lean_leansearch` surfaced the source-facing Chapter 29 flatness owner
-- `Scheme.Modules.flatOver`, the scoped pullback surface `f^*`, the standard module tensor
-- notation `⊗`, and the scheme-theoretic fiber owner `Scheme.Hom.fiber`; combined with the
-- local Chapter 31 owner `relativeAssassin`, the source union over
-- `s ∈ Ass_S(\mathcal G)` is expressed as
-- `relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢`.

/-- Lemma 31.3.1 (1): let `f : X ⟶ S` be a morphism of schemes, let `ℱ` be a quasi-coherent
`\mathcal O_X`-module flat over `S`, and let `𝒢` be a quasi-coherent `\mathcal O_S`-module.
Then `Ass_X(ℱ ⊗ f^*𝒢)` contains the union of the fiberwise associated points
`Ass_{X_s}(ℱ_s)` over `s ∈ Ass_S(𝒢)`. In Lean this source union is written as
`relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢`. -/
theorem relativeAssassin_inter_preimage_associatedPoints_subset_associatedPoints_tensor_pullback
    (hflat : flatOver ℱ f) :
    relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢 ⊆
      associatedPoints ((ℱ ⊗ ((f^*).obj 𝒢) : ModX)) := sorry

/-- Lemma 31.3.1 (2): with the hypotheses of Lemma `31.3.1 (1)`, if `S` is locally Noetherian,
then `Ass_X(ℱ ⊗ f^*𝒢)` is exactly the union of the fiberwise associated points
`Ass_{X_s}(ℱ_s)` over `s ∈ Ass_S(𝒢)`. In Lean this source union is written as
`relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢`. -/
theorem associatedPoints_tensor_pullback_eq_relativeAssassin_inter_preimage_associatedPoints
    (hflat : flatOver ℱ f)
    [IsLocallyNoetherian S] :
    associatedPoints ((ℱ ⊗ ((f^*).obj 𝒢) : ModX)) =
      relativeAssassin f ℱ ∩ f.base ⁻¹' associatedPoints 𝒢 := sorry

end AlgebraicGeometry.Scheme.Modules
