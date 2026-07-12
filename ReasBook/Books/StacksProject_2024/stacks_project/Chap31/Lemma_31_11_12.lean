import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1
import StacksProject_2024.Chap31.Lemma_31_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X]
variable [MonoidalCategory X.Modules] [MonoidalClosed X.Modules]

-- Semantic recall: `lean_leansearch` surfaced the canonical torsion-free owner
-- `Module.IsTorsionFree`; the scheme-level owner `IsTorsionFree`, the closed-structure object
-- `ihom`, and the finite-presentation owner were then verified locally against
-- `Lemma_31_11_3`, `Definition_31_12_1`, and the Chapter 18 internal-Hom files.

/-- Internal Hom out of a finitely presented quasi-coherent module into a quasi-coherent module on
an integral scheme is quasi-coherent. -/
instance isQuasicoherent_internalHom_of_isFinitePresentation
    (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℱ.IsFinitePresentation] :
    (((ihom ℱ).obj 𝒢)).IsQuasicoherent := sorry

/-- Lemma 31.11.12: let `X` be an integral scheme. Let `\mathcal F`, `\mathcal G` be
quasi-coherent `\mathcal O_X`-modules. If `\mathcal G` is torsion free and `\mathcal F` is of
finite presentation, then
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G)` is torsion free. -/
@[stacks 0AXZ]
theorem isTorsionFree_internalHom_of_isFinitePresentation
    (ℱ 𝒢 : X.Modules) [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent] [ℱ.IsFinitePresentation]
    [IsTorsionFree 𝒢] :
    IsTorsionFree (((ihom ℱ).obj 𝒢)) := sorry

end AlgebraicGeometry.Scheme.Modules
