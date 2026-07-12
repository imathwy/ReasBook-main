import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced `IsImmersion`, `IsClosedImmersion`, and the
separatedness diagonal criterion. Local precedent in Lemma 26.21.10 states the corresponding
graph-map result; this item specializes it to a section `s : S ⟶ X` with `s ≫ f = 𝟙 S`. -/

variable {X S : Scheme.{u}} (f : X ⟶ S) (s : S ⟶ X)

/-- Lemma 26.21.11 (1): a section `s : S ⟶ X` of a morphism `f : X ⟶ S` of schemes is an
immersion. -/
@[stacks 01KT]
theorem section_isImmersion (hs : s ≫ f = 𝟙 S) :
    IsImmersion s := sorry

/-- Lemma 26.21.11 (2): if `f : X ⟶ S` is separated, then every section
`s : S ⟶ X` of `f` is a closed immersion. -/
@[stacks 01KT]
theorem section_isClosedImmersion_of_isSeparated [IsSeparated f] (hs : s ≫ f = 𝟙 S) :
    IsClosedImmersion s := sorry

/-- Lemma 26.21.11 (3): if `f : X ⟶ S` is quasi-separated, then every section
`s : S ⟶ X` of `f` is quasi-compact. -/
@[stacks 01KT]
theorem section_quasiCompact_of_quasiSeparated [QuasiSeparated f] (hs : s ≫ f = 𝟙 S) :
    QuasiCompact s := sorry

end AlgebraicGeometry
