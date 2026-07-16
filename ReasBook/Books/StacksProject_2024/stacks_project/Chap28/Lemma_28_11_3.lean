import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_11_4
import StacksProject_2024.stacks_project.Chap05.Definition_5_20_1

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- `lean_leansearch` and `lean_local_search` were attempted for the catenary-scheme / local
-- dimension-function interface but both timed out in this environment, so the owner/API choice
-- below is verified from local precedents `Chap28/Definition_28_11_1`,
-- `Chap28/Lemma_28_11_2`, `Chap05/Lemma_5_20_4`, and `Chap28/Lemma_28_5_5`.

variable (S : Scheme.{u}) [IsLocallyNoetherian S]

/-- Lemma 28.11.3: for a locally Noetherian scheme `S`, the scheme is catenary if and only if
locally in the Zariski topology there exists a dimension function on `S`. Concretely, every point
of `S` admits an open neighbourhood whose induced topological space carries a dimension function. -/
theorem catenarySpace_iff_locally_exists_dimensionFunction :
    CatenarySpace S ↔
      ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := sorry

end AlgebraicGeometry
