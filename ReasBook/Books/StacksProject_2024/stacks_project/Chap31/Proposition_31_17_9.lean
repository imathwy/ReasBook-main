import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import StacksProject_2024.Chap28.Definition_28_7_1
import StacksProject_2024.Chap29.Lemma_29_45_6
import StacksProject_2024.Chap31.Lemma_31_17_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme morphism owners
`AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Surjective`. Local Section 31.17 precedent
uses `HasAmpleInvertibleSheaf` for the source phrase "has an ample invertible sheaf",
and local Chapter 29 precedent identifies the finite locally free condition with finite, flat, and
locally of finite presentation. Normality is recorded by `Scheme.isNormal`, while `Y_red -> Y` is
`Y.nilradical.subschemeι`. The Stacks tag evidence is consistent: tag `0BD4` comes from
`https://stacks.math.columbia.edu/tag/0BD4`. -/

/-- Proposition 31.17.9 (1): if `π : X -> Y` is finite surjective, `X` has an ample
invertible sheaf, and `π` is finite locally free, then `Y` has an ample invertible sheaf. The
finite locally free condition is represented by flatness and local finite presentation under the
ambient finite hypothesis. -/
@[stacks 0BD4]
theorem hasAmpleInvertibleSheaf_target_of_isFinite_surjective_flat_locallyOfFinitePresentation
    {X Y : Scheme} [CategoryTheory.MonoidalCategory X.Modules]
    [CategoryTheory.MonoidalCategory Y.Modules]
    (π : X ⟶ Y) [IsFinite π] [Surjective π] [Flat π] [LocallyOfFinitePresentation π]
    (hX : HasAmpleInvertibleSheaf X) :
    HasAmpleInvertibleSheaf Y := sorry

/-- Proposition 31.17.9 (2): if `π : X -> Y` is finite surjective, `X` has an ample
invertible sheaf, and `Y` is integral and normal, then `Y` has an ample invertible sheaf. -/
@[stacks 0BD4]
theorem hasAmpleInvertibleSheaf_target_of_isFinite_surjective_integral_normal
    {X Y : Scheme} [CategoryTheory.MonoidalCategory X.Modules]
    [CategoryTheory.MonoidalCategory Y.Modules]
    (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral Y] (hYnormal : Y.isNormal)
    (hX : HasAmpleInvertibleSheaf X) :
    HasAmpleInvertibleSheaf Y := sorry

/-- Proposition 31.17.9 (3): if `π : X -> Y` is finite surjective, `X` has an ample
invertible sheaf, `Y` is Noetherian, `p O_Y = 0` for a prime `p`, and `X` is the reduced
subscheme `Y_red` compatibly with `π`, then `Y` has an ample invertible sheaf. -/
@[stacks 0BD4]
theorem hasAmpleInvertibleSheaf_target_of_isFinite_surjective_noetherian_charP_isReduction
    {X Y : Scheme} [CategoryTheory.MonoidalCategory X.Modules]
    [CategoryTheory.MonoidalCategory Y.Modules]
    (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsNoetherian Y]
    (p : ℕ) (hp : Nat.Prime p)
    (hchar : ∀ (U : Y.Opens) (hU : IsAffineOpen U), (p : Γ(Y, U)) = 0)
    (e : X ≅ Y.nilradical.subscheme)
    (hπ : (e.hom ≫ Y.nilradical.subschemeι) = π)
    (hX : HasAmpleInvertibleSheaf X) :
    HasAmpleInvertibleSheaf Y := sorry

end AlgebraicGeometry.Scheme
