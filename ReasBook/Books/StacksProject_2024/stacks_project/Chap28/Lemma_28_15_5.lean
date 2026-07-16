import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped BigOperators

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` surfaced the canonical owners `irreducibleComponents` and
-- `minimalPrimes`, while the existing Chapter 28 branch-number API is stalkwise on `Scheme`.
-- This item is therefore stated on the stalk `X.presheaf.stalk x`, using the minimal primes of
-- that local ring to encode the irreducible components of `X` passing through `x`.

variable {X : Scheme.{u}} (x : X)

/-- Helper instance: the quotient of the stalk `X.presheaf.stalk x` by a minimal prime is a local
ring. -/
instance instIsLocalRingStalkQuotientMinimalPrime
    (p : {p : Ideal (X.presheaf.stalk x) // p ∈ minimalPrimes (X.presheaf.stalk x)}) :
    IsLocalRing ((X.presheaf.stalk x) ⧸ p.1) := sorry

/-- Lemma 28.15.5 (1): the branch number of a scheme `X` at a point `x` is the sum of the branch
numbers of the local rings of the irreducible components of `X` through `x`, expressed via the
minimal primes of the stalk `X.presheaf.stalk x`. -/
@[stacks 0E20]
theorem branchNumberAt_eq_tsum_branchNumber_quotientByMinimalPrimes
    (Ah : Type u) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah]
    (Ahp : {p : Ideal (X.presheaf.stalk x) // p ∈ minimalPrimes (X.presheaf.stalk x)} → Type u)
    [∀ p, CommRing (Ahp p)]
    [∀ p, Algebra ((X.presheaf.stalk x) ⧸ p.1) (Ahp p)]
    [∀ p, IsHenselizationOf ((X.presheaf.stalk x) ⧸ p.1) (Ahp p)] :
    X.branchNumberAt x Ah =
      ∑' p : {p : Ideal (X.presheaf.stalk x) // p ∈ minimalPrimes (X.presheaf.stalk x)},
        branchNumber ((X.presheaf.stalk x) ⧸ p.1) (Ahp p) := sorry

/-- Lemma 28.15.5 (2): the geometric branch number of a scheme `X` at a point `x` is the sum of
the geometric branch numbers of the local rings of the irreducible components of `X` through `x`,
expressed via the minimal primes of the stalk `X.presheaf.stalk x`. -/
@[stacks 0E20]
theorem geometricBranchNumberAt_eq_tsum_geometricBranchNumber_quotientByMinimalPrimes
    (Ash : Type u) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash]
    (Ashp : {p : Ideal (X.presheaf.stalk x) // p ∈ minimalPrimes (X.presheaf.stalk x)} → Type u)
    [∀ p, CommRing (Ashp p)]
    [∀ p, Algebra ((X.presheaf.stalk x) ⧸ p.1) (Ashp p)]
    [∀ p, IsStrictHenselizationOf ((X.presheaf.stalk x) ⧸ p.1) (Ashp p)] :
    X.geometricBranchNumberAt x Ash =
      ∑' p : {p : Ideal (X.presheaf.stalk x) // p ∈ minimalPrimes (X.presheaf.stalk x)},
        geometricBranchNumber ((X.presheaf.stalk x) ⧸ p.1) (Ashp p) := sorry

end AlgebraicGeometry.Scheme
