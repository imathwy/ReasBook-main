import Mathlib.Data.Set.Function
import Mathlib.Geometry.Manifold.Diffeomorph
import SmoothManifoldsLee.Chap04.Sec04_25.Proposition_4_28

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

namespace Manifold

universe uK uE uE1 uE2 uH uH1 uH2 uM uN1 uN2

variable {k : Type uK} [NontriviallyNormedField k]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace k E]
variable {E1 : Type uE1} [NormedAddCommGroup E1] [NormedSpace k E1]
variable {E2 : Type uE2} [NormedAddCommGroup E2] [NormedSpace k E2]
variable {H : Type uH} [TopologicalSpace H]
variable {H1 : Type uH1} [TopologicalSpace H1]
variable {H2 : Type uH2} [TopologicalSpace H2]
variable {I : ModelWithCorners k E H}
variable {J1 : ModelWithCorners k E1 H1}
variable {J2 : ModelWithCorners k E2 H2}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N1 : Type uN1} [TopologicalSpace N1] [ChartedSpace H1 N1] [IsManifold J1 ∞ N1]
variable {N2 : Type uN2} [TopologicalSpace N2] [ChartedSpace H2 N2] [IsManifold J2 ∞ N2]

-- Proof sketch: use `hpi1.isQuotientMap hsurj1` to descend `pi2` to a continuous map
-- `F : N1 → N2`, since `hfib12` says that `pi2` is constant on the fibers of `pi1`. Likewise use
-- `hpi2.isQuotientMap hsurj2` and `hfib21` to descend `pi1` to the inverse map `N2 → N1`,
-- yielding a homeomorphism of targets. Smoothness of the descended maps follows by pulling back
-- along the surjective submersions and using the smooth-local-section criterion from the chapter.
-- Uniqueness follows from the surjectivity of `pi1` together with `Diffeomorph.ext`.
/-- Theorem 4.31 (Uniqueness of Smooth Quotients): surjective smooth submersions from a common
smooth manifold that are constant on each other's fibers determine a unique diffeomorphism between
their targets intertwining the quotient maps. -/
theorem existsUnique_diffeomorph_of_surjective_smooth_submersions_constant_on_each_others_fibers
    {pi1 : M → N1} {pi2 : M → N2} (hpi1 : IsSmoothSubmersion I J1 pi1)
    (hpi2 : IsSmoothSubmersion I J2 pi2)
    (hsurj1 : Function.Surjective pi1) (hsurj2 : Function.Surjective pi2)
    (hfib12 : ∀ x y : M, pi1 x = pi1 y → pi2 x = pi2 y)
    (hfib21 : ∀ x y : M, pi2 x = pi2 y → pi1 x = pi1 y) :
    ∃! F : N1 ≃ₘ⟮J1, J2⟯ N2, F ∘ pi1 = pi2 := sorry

end Manifold
