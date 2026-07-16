import Mathlib
import StacksProject_2024.stacks_project.Chap28.Lemma_28_13_8
import StacksProject_2024.stacks_project.Chap29.Lemma_29_15_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- `lean_leansearch` recalled `Scheme.Hom.fromNormalization` and `AlgebraicGeometry.IsFinite` as
-- the canonical relative-normalization finiteness owners. Local Chapter 29 precedent packages
-- “`f` is of finite type” as `[QuasiCompact f] [LocallyOfFiniteType f]`, while
-- `Scheme.Nagata S` supplies the locally Noetherian base needed to recover quasi-separatedness.

/-- A morphism locally of finite type over a Nagata base is quasi-separated. -/
@[stacks 03GR]
instance instQuasiSeparatedOfLocallyOfFiniteTypeOverNagata {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [Scheme.Nagata S] :
    QuasiSeparated f :=
  quasiSeparated_of_locallyOfFiniteType f

/-- Lemma 29.53.15: let `f : X ⟶ S` be a morphism. Assume that `S` is a Nagata scheme, `f` is of
finite type, and `X` is reduced. Then the normalization `ν : S' ⟶ S` of `S` in `X`, formalized as
`f.fromNormalization`, is finite. -/
@[stacks 03GR]
theorem Scheme.Hom.isFinite_fromNormalization_of_nagata_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [LocallyOfFiniteType f]
    [Scheme.Nagata S] [IsReduced X] :
    IsFinite f.fromNormalization := sorry

end AlgebraicGeometry
