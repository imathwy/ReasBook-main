import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `UniversallyClosed`,
-- `universallyClosed_iff`, `universallyClosed_eq_universallySpecializing`, and
-- `SpecializingMap`. Local Chapter 26 precedent uses `SpecializingMap f.base` for
-- "specializations lift along `f`", so this item is stated directly for the canonical
-- base-change maps `pullback.snd f g`.

section

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Lemma 26.20.2 (1): if a morphism of schemes is universally closed, then specializations
lift along every base change of it. -/
@[stacks 01KC]
theorem UniversallyClosed.specializingMap_baseChange (hf : UniversallyClosed f) :
    ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), SpecializingMap (pullback.snd f g).base := sorry

/-- Lemma 26.20.2 (2): if a quasi-compact morphism of schemes has specialization lifting after
every base change, then it is universally closed. -/
@[stacks 01KC]
theorem universallyClosed_of_quasiCompact_specializingMap_baseChange [QuasiCompact f]
    (hf : ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S), SpecializingMap (pullback.snd f g).base) :
    UniversallyClosed f := sorry

end

end AlgebraicGeometry
