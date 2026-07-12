import StacksProject_2024.Chap31.Lemma_31_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical finite-morphism owner
`AlgebraicGeometry.IsFinite` and the quasi-affine owner `Scheme.IsQuasiAffine`. Local Chapter 31
precedent records norms for this section as `FiniteMorphismNorm` with property
`IsFiniteMorphismNorm`. The Stacks tag evidence is consistent: tag `0BD1` comes from
`https://stacks.math.columbia.edu/tag/0BD1`. -/

/-- Lemma 31.17.5: let `π : X ⟶ Y` be a finite morphism of schemes. Assume `X` is
quasi-affine and there exists a norm of degree `d` for `π`. Then `Y` is quasi-affine. -/
@[stacks 0BD1]
theorem isQuasiAffine_target_of_isFinite_of_isQuasiAffine_of_exists_finiteMorphismNorm
    {X Y : Scheme} (π : X ⟶ Y) [IsFinite π] (d : ℕ)
    (hX : X.IsQuasiAffine)
    (hnorm : ∃ N : FiniteMorphismNorm π, IsFiniteMorphismNorm π d N) :
    Y.IsQuasiAffine := sorry

end AlgebraicGeometry.Scheme
