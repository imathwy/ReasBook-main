import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_24_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Semantic recall / local owner check:
-- `lean_leansearch` only surfaced general support/closed-subset infrastructure, while the
-- dependency `Chap28/Lemma_28_24_5` already formalizes the actual quasi-coherent subsheaf as
-- `sectionsWithSupportIn Z ℱ`; this item is therefore a recall-only naming entry, not a new alias.

/- Definition 28.24.6: for a closed subset `T ⊆ X` whose open complement is retrocompact and a
quasi-coherent `\mathcal{O}_X`-module `ℱ`, the quasi-coherent subsheaf defined in Lemma 28.24.5
is the existing owner `sectionsWithSupportIn T ℱ`, called the subsheaf of sections supported on
`T`. -/
#check sectionsWithSupportIn

/- Companion recall: Lemma 28.24.5 already proves the quasi-coherence of
`sectionsWithSupportIn T ℱ` under the retrocompactness hypothesis on the open complement. -/
#check sectionsWithSupportIn_isQuasicoherent

end AlgebraicGeometry.Scheme.Modules
