import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` only surfaced the ambient closed-monoidal sheaf owners, so
-- the final statement shape was checked against local Chapter 17 precedent:
-- `SheafOfModules.RingedSite.isCoherent_ringedSiteModuleTensor`,
-- `RingedSpace.internalHom_isCoherent_of_isFinitePresentation`, and the coherent-versus-finite-
-- presentation bridge on coherent structure sheaves.

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules]
variable [MonoidalClosed X.Modules]
variable {ℱ 𝒢 : X.Modules}

local notation "ModX" => X.Modules
local notation:70 A " ⊗ₘ " B => (tensorObj A B : ModX)

/-- Lemma 30.9.4 (1): if `X` is a locally Noetherian scheme and `\mathcal F`, `\mathcal G` are
coherent `\mathcal O_X`-modules, then
`\mathcal F \otimes_{\mathcal O_X} \mathcal G` is coherent. -/
@[stacks 01Y2]
theorem isCoherent_tensor
    [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (ℱ ⊗ₘ 𝒢).IsCoherent := sorry

/-- Lemma 30.9.4 (2): if `X` is a locally Noetherian scheme and `\mathcal F`, `\mathcal G` are
coherent `\mathcal O_X`-modules, then
`\mathcal{H}\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G)` is coherent. -/
@[stacks 01Y2]
theorem isCoherent_internalHom
    [ℱ.IsCoherent] [𝒢.IsCoherent] :
    ((ihom ℱ).obj 𝒢).IsCoherent := sorry

end AlgebraicGeometry.Scheme.Modules
