import StacksProject_2024.stacks_project.Chap30.Lemma_30_18_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme-morphism owners `IsProper`,
`IsSeparated`, and `Scheme.Hom.FiniteType`. Local precedent uses `ChowLemmaModification` for the
Chow-lemma diagram with a dense open isomorphism, and `Finite (irreducibleComponents X)` for
“finitely many irreducible components”. The Stacks tag evidence is consistent: item tag `0203`
agrees with the source URL ending in `/tag/0203`. -/

/-- Lemma 32.12.3: let `S` be quasi-compact and quasi-separated, and let `f : X ⟶ S` be a
separated morphism of finite type. If `X` has finitely many irreducible components, then there is
a diagram `X ← X' → \mathbf P^n_S → S` in which `X' ⟶ \mathbf P^n_S` is an immersion and
`π : X' ⟶ X` is proper and surjective. Moreover, `π` is an isomorphism over a dense open
subscheme of `X`. -/
@[stacks 0203]
theorem exists_projectiveSpaceImmersion_proper_surjective_isoOverDenseOpen_of_separated_finiteType_qcqs_finiteIrreducibleComponents
    {X S : Scheme.{u}} (f : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
    [IsSeparated f] [Scheme.Hom.FiniteType f] [Finite (irreducibleComponents X)] :
    Nonempty (ChowLemmaModification f) := sorry

end AlgebraicGeometry
