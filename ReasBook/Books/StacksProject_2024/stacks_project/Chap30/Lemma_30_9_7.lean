import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.support` and
-- `Scheme.Modules.pushforward`; local Chapter 29 precedent fixes scheme-theoretic support as
-- the affine-open annihilator condition of `IsSchemeTheoreticSupport ℱ I` and ordinary sheaf
-- support as `moduleSupport ℱ`.

/-- Lemma 30.9.7 (1): let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then `Supp(ℱ)` is closed. -/
@[stacks 01Y5]
theorem isClosed_moduleSupport_of_isCoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    IsClosed (moduleSupport ℱ) := sorry

/-- Lemma 30.9.7 (2): let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. For any scheme-theoretic support `I` of `ℱ`, the module `ℱ` comes from
a coherent sheaf on the closed subscheme `I.subscheme`. -/
@[stacks 01Y5]
theorem exists_isCoherent_on_schemeTheoreticSupport
    (ℱ : X.Modules) [ℱ.IsCoherent]
    (I : X.IdealSheafData)
    (hI : IsSchemeTheoreticSupport ℱ I) :
    ∃ 𝒢 : I.subscheme.Modules, ∃ _ : 𝒢.IsCoherent,
      Nonempty ((pushforward I.subschemeι).obj 𝒢 ≅ ℱ) := sorry

end AlgebraicGeometry.Scheme.Modules
