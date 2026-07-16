import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_5_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `CategoryTheory.ShortComplex.ShortExact` as the
-- canonical exact-sequence owner, while local Chapter 17/30 precedent already uses
-- `moduleSupport` for sheaf support and `SheafOfModules.IsCoherent` for coherence. The closed
-- pieces are recorded as `TopologicalSpace.Closeds X`, matching the source's closed-subset input.

variable {X : Scheme.{u}} [IsNoetherian X]

/-- Lemma 30.12.1: if the support of a coherent `\mathcal O_X`-module `ℱ` on a Noetherian scheme
is the union of two closed subsets `Z` and `Z'`, then there exist coherent sheaves `𝒢'` and `𝒢`
fitting into a short exact sequence `0 \to 𝒢' \to ℱ \to 𝒢 \to 0` with
`Supp(𝒢') ⊆ Z'` and `Supp(𝒢) ⊆ Z`. -/
@[stacks 01YD]
theorem exists_shortExact_of_support_eq_union
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (Z Z' : TopologicalSpace.Closeds X)
    (hSupp : moduleSupport ℱ = (Z : Set X) ∪ (Z' : Set X)) :
    ∃ (𝒢' 𝒢 : X.Modules) (_h𝒢' : SheafOfModules.IsCoherent 𝒢')
      (_h𝒢 : SheafOfModules.IsCoherent 𝒢)
      (ι : 𝒢' ⟶ ℱ) (π : ℱ ⟶ 𝒢) (w : ι ≫ π = 0)
      (_hSupp𝒢 : moduleSupport 𝒢 ⊆ (Z : Set X)),
      (ShortComplex.mk ι π w).ShortExact ∧
        moduleSupport 𝒢' ⊆ (Z' : Set X) := sorry

end AlgebraicGeometry.Scheme.Modules
