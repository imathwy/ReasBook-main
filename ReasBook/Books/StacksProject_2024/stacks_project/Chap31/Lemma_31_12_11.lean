import StacksProject_2024.Chap30.Definition_30_11_1
import StacksProject_2024.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped ENat

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the ring/module owners `Module.IsReflexive` and
-- `Module.SerreConditionS`. Local precedent in `Chap15/Lemma_15_23_16.lean`,
-- `Chap30/Definition_30_11_1.lean`, and `Chap31/Lemma_31_12_4.lean` fixes the scheme-level API as
-- a stalkwise depth theorem together with the chapter-local scheme/sheaf predicates
-- `Scheme.satisfiesSerreConditionS` and `Scheme.Modules.satisfiesSerreConditionS`.

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

namespace IsReflexive

/-- Lemma 31.12.11 (1): let `X` be an integral locally Noetherian scheme, let `ℱ` be a coherent
reflexive `\mathcal O_X`-module, and let `x : X`. If
`depth(\mathcal O_{X, x}) \ge 2`, then `depth(\mathcal F_x) \ge 2`. -/
@[stacks 0EBI]
theorem moduleDepth_stalk_ge_two_of_ringDepth_stalk_ge_two
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ] (x : X)
    (hx : (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (X.presheaf.stalk x)) :
    (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat ℱ x) := sorry

/-- Lemma 31.12.11 (2): let `X` be an integral locally Noetherian scheme and let `ℱ` be a
coherent reflexive `\mathcal O_X`-module. If `X` satisfies `(S_2)`, then `ℱ` satisfies `(S_2)`. -/
@[stacks 0EBI]
theorem satisfiesSerreConditionS_two
    (ℱ : X.Modules) [ℱ.IsCoherent] [IsReflexive ℱ]
    (hX : X.satisfiesSerreConditionS 2) :
    satisfiesSerreConditionS ℱ 2 := sorry

end IsReflexive

end

end AlgebraicGeometry.Scheme.Modules
