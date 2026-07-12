import StacksProject_2024.Chap32.Lemma_32_9_3
import StacksProject_2024.Chap29.Definition_29_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners
-- `IsClosedImmersion`, `LocallyOfFiniteType`, and `LocallyOfFinitePresentation`. Local Section
-- 32.9 already packages the finite-presentation closed-immersion factorization, while the Stacks
-- source tag evidence is consistent with tag `01ZJ`.

/-- Proposition 32.9.6: let `f : X ⟶ S` be a morphism of schemes. Assume `f` is of finite type
and separated, and `S` is quasi-compact and quasi-separated. Then there exists a separated
morphism of finite presentation `f' : X' ⟶ S` and a closed immersion `X ⟶ X'` over `S`. -/
@[stacks 01ZJ]
theorem exists_separated_finitePresentation_closedImmersion_factorization_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsSeparated f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    ∃ (X' : Scheme.{u}) (i : X ⟶ X') (f' : X' ⟶ S),
      FinitePresentationClosedImmersionFactorization f i f' ∧ IsSeparated f' := sorry

end AlgebraicGeometry
