import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Construction_20_1_4
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.LinearAlgebra.Quotient.Bilinear

open AlgebraicTopology
open scoped Manifold

noncomputable section

section

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {n : ℕ}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M]
variable [Fact (Module.finrank ℝ E = n)]

/-- The torsion submodule of integral singular cohomology in degree `p`. -/
abbrev integralSingularCohomologyTorsion (X : TopCat) (p : ℕ) :
    Submodule ℤ (integralSingularCohomology X p) :=
  Submodule.torsion ℤ (integralSingularCohomology X p)

/-- Integral singular cohomology in degree `p`, quotiented by its torsion submodule. -/
abbrev integralSingularCohomologyModTorsion (X : TopCat) (p : ℕ) :=
  integralSingularCohomology X p ⧸ integralSingularCohomologyTorsion X p

/-- The quotient `integralSingularCohomologyModTorsion X p` inherits its canonical quotient
`ℤ`-module structure. -/
instance integralSingularCohomologyModTorsionModule (X : TopCat) (p : ℕ) :
    Module ℤ (integralSingularCohomologyModTorsion X p) :=
  Submodule.Quotient.module (integralSingularCohomologyTorsion X p)

/-- Every torsion class in the left variable is annihilated by the Construction 20.1.4 pairing. -/
theorem integralSingularCohomologyTorsion_le_leftKer_cupProductFundamentalClassPairing
    (o : ROrientedManifold ℤ I n M)
    (z : rSingularHomology ℤ n (TopCat.of M))
    (hz : IsRFundamentalClassFor o z)
    (p : ℕ) (hpn : p ≤ n) :
    integralSingularCohomologyTorsion (TopCat.of M) p ≤
      (cupProductTopHomologyClassPairing z p hpn).ker := sorry

/-- Every torsion class in the right variable is annihilated by the Construction 20.1.4 pairing. -/
theorem integralSingularCohomologyTorsion_le_rightKer_cupProductFundamentalClassPairing
    (o : ROrientedManifold ℤ I n M)
    (z : rSingularHomology ℤ n (TopCat.of M))
    (hz : IsRFundamentalClassFor o z)
    (p : ℕ) (hpn : p ≤ n) :
    integralSingularCohomologyTorsion (TopCat.of M) (n - p) ≤
      (cupProductTopHomologyClassPairing z p hpn).flip.ker := sorry

/-- The Construction 20.1.4 cup-product pairing descends to the torsion-free quotients of the two
complementary-degree cohomology groups. -/
noncomputable def cupProductFundamentalClassPairingModTorsion
    (o : ROrientedManifold ℤ I n M)
    (z : rSingularHomology ℤ n (TopCat.of M))
    (hz : IsRFundamentalClassFor o z)
    (p : ℕ) (hpn : p ≤ n) :=
  (cupProductTopHomologyClassPairing z p hpn).liftQ₂
    (integralSingularCohomologyTorsion (TopCat.of M) p)
    (integralSingularCohomologyTorsion (TopCat.of M) (n - p))
    (integralSingularCohomologyTorsion_le_leftKer_cupProductFundamentalClassPairing
      o z hz p hpn)
    (integralSingularCohomologyTorsion_le_rightKer_cupProductFundamentalClassPairing
      o z hz p hpn)

/-- Applying the descended quotient pairing to classes represented by `α` and `β` recovers the
original Construction 20.1.4 pairing on those representatives. -/
@[simp]
theorem cupProductFundamentalClassPairingModTorsion_apply
    (o : ROrientedManifold ℤ I n M)
    (z : rSingularHomology ℤ n (TopCat.of M))
    (hz : IsRFundamentalClassFor o z)
    (p : ℕ) (hpn : p ≤ n)
    (α : integralSingularCohomology (TopCat.of M) p)
    (β : integralSingularCohomology (TopCat.of M) (n - p)) :
    cupProductFundamentalClassPairingModTorsion o z hz p hpn
        (Submodule.Quotient.mk α)
        (Submodule.Quotient.mk β) =
      cupProductTopHomologyClassPairing z p hpn α β := by
  rfl

/-- Corollary 20.1.5. For integral coefficients, the cup product pairing is nonsingular after
quotienting complementary-degree cohomology by torsion on both sides. Here "nonsingular" is
formalized by `LinearMap.IsPerfPair` for the descended pairing
`cupProductFundamentalClassPairingModTorsion`. -/
instance cupProductFundamentalClassPairingModTorsion_isPerfPair
    (o : ROrientedManifold ℤ I n M)
    (z : rSingularHomology ℤ n (TopCat.of M))
    (hz : IsRFundamentalClassFor o z)
    (p : ℕ) (hpn : p ≤ n) :
    (cupProductFundamentalClassPairingModTorsion o z hz p hpn).IsPerfPair := sorry

end
