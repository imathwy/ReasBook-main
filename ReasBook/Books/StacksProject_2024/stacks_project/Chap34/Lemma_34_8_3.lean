import Mathlib.AlgebraicGeometry.Cover.Open
import StacksProject_2024.Chap34.Definition_34_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` suggested `Scheme.OpenCover.affineRefinement` and
-- `Scheme.OpenCover`; local Chapter 34 uses `StandardPhCovering` as the source-facing owner for
-- standard ph coverings.

/-- Lemma 34.8.3 (1): if `T` is affine, every Zariski open covering of `T` admits a refinement by
a standard ph covering. The displayed factorization says that each affine member of the standard
ph covering maps through one member of the original open cover. -/
@[stacks 0DBF]
theorem exists_standardPhCovering_refining_zariskiOpenCover
    {T : Scheme.{u}} [IsAffine T] (𝒰 : T.OpenCover) :
    ∃ Φ : StandardPhCovering T,
      ∀ j : Fin Φ.m, ∃ i : 𝒰.I₀, ∃ g : Φ.obj j ⟶ 𝒰.X i,
        g ≫ 𝒰.f i = Φ.map j := sorry

/-- Lemma 34.8.3 (2): if `{U_j ⟶ T}` is a standard ph covering of an affine scheme and each
`U_j` has a standard ph covering `{W_{ji} ⟶ U_j}`, then the composite family
`{W_{ji} ⟶ T}` admits a refinement by a standard ph covering. -/
@[stacks 0DBF]
theorem exists_standardPhCovering_refining_standardPhComposite
    {T : Scheme.{u}} [IsAffine T] (Φ : StandardPhCovering T)
    (Ψ : ∀ j : Fin Φ.m, StandardPhCovering (Φ.obj j)) :
    ∃ Ω : StandardPhCovering T,
      ∀ k : Fin Ω.m,
        ∃ p : Sigma fun j : Fin Φ.m ↦ Fin (Ψ j).m,
          ∃ g : Ω.obj k ⟶ (Ψ p.1).obj p.2,
            g ≫ (Ψ p.1).map p.2 ≫ Φ.map p.1 = Ω.map k := sorry

end AlgebraicGeometry
