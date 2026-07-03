import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_61

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

open Metric

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- Semantic search note: `lean_leansearch` was unavailable in this environment, so the owner/API
-- choice was verified against `Lemma_10_61` and nearby Chapter 10 files.

/- Definition 10.63 is recall-only: the source-faithful `arg max` characterization of the owner
set `Λ[a]` already lives in the owner file `Lemma_10_61` as `mem_Λ_iff`. -/
recall mem_Λ_iff

end
