import StacksProject_2024.stacks_project.Chap31.Lemma_31_15_12
import StacksProject_2024.stacks_project.Chap31.Lemma_31_17_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical finite-morphism owner
`AlgebraicGeometry.IsFinite`. Local Chapter 31 precedent records norms for this section as
`FiniteMorphismNorm` with property `IsFiniteMorphismNorm`, while Lemma 31.15.12 provides the
dependency-closed owner `HasAmpleInvertibleSheaf` for the source phrase "has an ample
invertible sheaf". The Stacks tag evidence is consistent: tag `0BD0` comes from
`https://stacks.math.columbia.edu/tag/0BD0`. -/

/-- Lemma 31.17.4: let `π : X ⟶ Y` be a finite morphism of schemes. Assume `X` has an ample
invertible sheaf and there exists a norm of degree `d` for `π`. Then `Y` has an ample
invertible sheaf. -/
@[stacks 0BD0]
theorem hasAmpleInvertibleSheaf_target_of_isFinite_of_exists_finiteMorphismNorm
    {X Y : Scheme} [CategoryTheory.MonoidalCategory X.Modules]
    [CategoryTheory.MonoidalCategory Y.Modules]
    (π : X ⟶ Y) [IsFinite π] (d : ℕ)
    (hX : HasAmpleInvertibleSheaf X)
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    HasAmpleInvertibleSheaf Y := sorry

end AlgebraicGeometry.Scheme
