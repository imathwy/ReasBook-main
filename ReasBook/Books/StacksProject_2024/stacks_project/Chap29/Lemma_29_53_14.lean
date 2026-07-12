import Mathlib
import StacksProject_2024.Chap28.Lemma_28_13_8
import StacksProject_2024.Chap29.Definition_29_10_1
import StacksProject_2024.Chap29.Definition_29_50_1
import StacksProject_2024.Chap29.Remark_29_49_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall / local analogue check:
-- `lean_leansearch` identified the canonical relative-normalization owner
-- `Scheme.Hom.fromNormalization` in `Mathlib.AlgebraicGeometry.Normalization`. Chapter 29 already
-- exports the residue-field algebra owner `Scheme.Hom.residueFieldAlgebra`, and the source-facing
-- generic-point owner is `genericPointsOfIrreducibleComponents`, so this lemma is stated directly
-- with those existing APIs.

/- Lemma 29.53.14 (Stacks tag `0AVK`): let `f : X ⟶ S` be a morphism. Assume that `S` is a
Nagata scheme, `f` is quasi-compact and quasi-separated, quasi-compact opens of `X` have finitely
many irreducible components, for every generic point `x` of an irreducible component of `X` the
residue-field extension `κ(x) / κ(f(x))` is finitely generated, and `X` is reduced. Then the
normalization `ν : S' ⟶ S` of `S` in `X`, formalized as `f.fromNormalization`, is finite. -/
@[stacks 0AVK]
theorem Scheme.Hom.isFinite_fromNormalization_of_nagata
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [Scheme.Nagata S] [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X] [IsReduced X]
    (hfg :
      ∀ x : X, x ∈ genericPointsOfIrreducibleComponents X →
        Algebra.FiniteType (S.residueField (f x)) (X.residueField x)) :
    IsFinite f.fromNormalization := sorry

end AlgebraicGeometry
