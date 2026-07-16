import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the canonical sheaf predicate
-- `SheafOfModules.IsQuasicoherent` and the algebraic submodule/quotient Noetherian finiteness
-- owner `isNoetherian_iff_submodule_quotient`. Local Chapter 30 precedent represents
-- submodules by `Subobject ℱ`, so quotient modules are represented by epimorphisms out of `ℱ`.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- Lemma 30.9.3 (1): let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Any quasi-coherent submodule of `ℱ` is coherent. -/
@[stacks 01Y1]
theorem isCoherent_subobject_of_isQuasicoherent
    (ℱ : X.Modules) [ℱ.IsCoherent] (𝒢 : Subobject ℱ)
    [((𝒢 : X.Modules)).IsQuasicoherent] :
    ((𝒢 : X.Modules)).IsCoherent := sorry

/-- Lemma 30.9.3 (2): let `X` be a locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Any quasi-coherent quotient module of `ℱ` is coherent. -/
@[stacks 01Y1]
theorem isCoherent_of_epi_from_coherent
    {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]
    (π : ℱ ⟶ 𝒢) [Epi π] :
    𝒢.IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
