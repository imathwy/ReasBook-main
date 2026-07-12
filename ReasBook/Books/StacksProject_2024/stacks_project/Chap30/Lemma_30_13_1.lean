import Mathlib
import StacksProject_2024.Chap17.Definition_17_5_1
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the scheme-morphism owners `IsFinite`,
-- `Surjective`, and `Scheme.Modules.pushforward`; nearby Chapter 17/30 files use
-- `moduleSupport` and `SheafOfModules.IsCoherent` for the sheaf-side support and coherence.

/-- Lemma 30.13.1: let `f : Y ⟶ X` be finite and surjective with `X` locally Noetherian, and
let `Z ⊆ X` be an integral closed subscheme with generic point `ξ`. There exists a coherent
`\mathcal O_Y`-module `ℱ` such that `Supp(f_* ℱ) = Z` as a subset of `X`, and the stalk
`(f_* ℱ)_ξ` is annihilated by the maximal ideal `\mathfrak m_ξ`. -/
@[stacks 01YO]
theorem exists_coherent_pushforward_support_eq_and_stalk_annihilated
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] [Surjective f] [IsLocallyNoetherian X]
    (Z : X.IdealSheafData) [IsIntegral Z.subscheme]
    (ξ : X) (hξ : IsGenericPoint ξ (Z.support : Set X)) :
    ∃ ℱ : Y.Modules,
      ∃ _ : ℱ.IsCoherent,
        ∃ _ : moduleSupport ((Scheme.Modules.pushforward f).obj ℱ) = (Z.support : Set X),
          (∀ r : X.presheaf.stalk ξ,
            r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) →
              ∀ m : (RingedSpace.stalkModuleCat ((Scheme.Modules.pushforward f).obj ℱ) ξ),
                r • m = 0) := sorry

end AlgebraicGeometry.Scheme.Modules
