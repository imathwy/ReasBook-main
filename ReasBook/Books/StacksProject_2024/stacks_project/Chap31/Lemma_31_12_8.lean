import StacksProject_2024.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `Scheme.Modules.Hom` and `Module.IsReflexive`; local
-- Chapter 31 precedent fixes the scheme-side internal Hom as `((ihom ℱ).obj 𝒢)`, while
-- `Chap15/Lemma_15_23_8.lean` supplies the ring-level analogue `isReflexive_linearMap`.

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]

/-- Lemma 31.12.8: let `X` be an integral locally Noetherian scheme. Let `\mathcal F`,
`\mathcal G` be coherent `\mathcal O_X`-modules. If `\mathcal G` is reflexive, then
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F, \mathcal G)` is reflexive. -/
@[stacks 0AY4]
theorem isReflexive_internalHom (h𝒢 : IsReflexive 𝒢) :
    IsReflexive ((ihom ℱ).obj 𝒢) := sorry

/-- Companion form of Lemma 31.12.8 for downstream `have`/`exact` use under an instance
assumption on `𝒢`. -/
theorem isReflexive_internalHom_of_inst [IsReflexive 𝒢] :
    IsReflexive ((ihom ℱ).obj 𝒢) :=
  isReflexive_internalHom ℱ 𝒢 inferInstance

end

end AlgebraicGeometry.Scheme.Modules
