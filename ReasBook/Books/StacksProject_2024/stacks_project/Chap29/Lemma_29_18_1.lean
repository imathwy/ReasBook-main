import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_13_8
import StacksProject_2024.stacks_project.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall / local analogue check:
-- `lean_leansearch` surfaced the canonical scheme-morphism owner `LocallyOfFiniteType` together
-- with the locally Noetherian transfer `LocallyOfFiniteType.isLocallyNoetherian`. The source-
-- facing scheme owners in this section are `Scheme.UniversallyJapanese` and `Scheme.Nagata`; the
-- corresponding ring-level permanence inputs are `universallyJapaneseRing_of_essFiniteType` and
-- `nagataRing_of_finiteType`.

/-- Lemma 29.18.1 (2): if `f : X ⟶ S` is locally of finite type and `S` is universally Japanese,
then `X` is universally Japanese. -/
@[stacks 035A]
theorem universallyJapanese_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [UniversallyJapanese S] :
    UniversallyJapanese X := sorry

/-- Lemma 29.18.1 (1): if `f : X ⟶ S` is locally of finite type and `S` is Nagata, then `X` is
Nagata. -/
@[stacks 035A]
theorem nagata_of_locallyOfFiniteType {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [Nagata S] :
    Nagata X := sorry

end AlgebraicGeometry.Scheme
