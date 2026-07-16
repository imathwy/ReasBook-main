import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_24_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable [MonoidalCategory (SheafOfModules X.ringCatSheaf)]
variable [MonoidalClosed (SheafOfModules X.ringCatSheaf)]

local notation "ModX" => SheafOfModules X.ringCatSheaf

variable (I : X.IdealSheafData) (ℱ : ModX)

-- Semantic recall / local owner check:
-- `lean_leansearch` surfaced only general ideal-sheaf-data infrastructure, while the dependency
-- `Chap28/Lemma_28_24_2` already introduces the actual subsheaf owner
-- `idealTorsionSubsheaf I ℱ`; this item is therefore a recall-only naming entry, not a new alias.

/- Definition 28.24.3: let `X` be a scheme, let `\mathcal I \subset \mathcal O_X` be a
quasi-coherent sheaf of ideals of finite type, and let `\mathcal F` be a quasi-coherent
`\mathcal O_X`-module. The subsheaf defined in Lemma 28.24.2 is the existing owner
`idealTorsionSubsheaf I ℱ`, called the subsheaf of sections annihilated by `\mathcal I`. -/
#check idealTorsionSubsheaf I ℱ

/- Companion recall: Lemma 28.24.2 already proves that under the source finite-type hypothesis on
`\mathcal I`, the subsheaf `idealTorsionSubsheaf I ℱ` is quasi-coherent when `ℱ` is
quasi-coherent. -/
#check idealTorsionSubsheaf_isQuasicoherent

end AlgebraicGeometry.Scheme.Modules
