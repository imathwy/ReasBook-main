import StacksProject_2024.Chap31.Definition_31_12_1
import StacksProject_2024.Chap31.Definition_31_11_2
import StacksProject_2024.Chap30.Lemma_30_9_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` returned the canonical module-level owners
-- `Module.IsReflexive.to_isTorsionFree` and `eval_injective_iff_isTorsionFree`. The scheme-level
-- surface below therefore keeps the existing Chapter 31 owners `IsReflexive`, `IsTorsionFree`,
-- and `toReflexiveHull`, while reusing the already-canonical coherence-to-quasi-coherence bridge
-- via instance search rather than introducing a duplicate local owner.

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

local instance instIsQuasicoherentOfIsCoherentForLemma31124 : ℱ.IsQuasicoherent := by
  let _ : ℱ.IsFinitePresentation :=
    (isCoherent_iff_isFinitePresentation (X := X) ℱ).mp inferInstance
  infer_instance

namespace IsReflexive

/-- Lemma 31.12.4 (1): let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
reflexive `\mathcal O_X`-module. Then `ℱ` is torsion free. -/
@[stacks 0AY2]
theorem isTorsionFree
    [IsReflexive ℱ] :
    IsTorsionFree ℱ := sorry

end IsReflexive

/-- Lemma 31.12.4 (2): let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then the canonical map `j : \mathcal F \to \mathcal F^{**}` is injective
if and only if `ℱ` is torsion free. -/
@[stacks 0AY2]
theorem mono_toReflexiveHull_iff_isTorsionFree
    :
    Mono (toReflexiveHull ℱ) ↔ IsTorsionFree ℱ := sorry

end

end AlgebraicGeometry.Scheme.Modules
