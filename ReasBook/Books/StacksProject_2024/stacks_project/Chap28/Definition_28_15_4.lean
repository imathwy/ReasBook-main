import Mathlib.AlgebraicGeometry.Stalk
import StacksProject_2024.stacks_project.Chap15.Definition_15_107_6

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` and a direct local probe confirmed that the canonical
-- ring-level owners are `branchNumber` and `geometricBranchNumber`, while the scheme-side local
-- ring is `X.presheaf.stalk x`. This item is therefore a stalkwise bridge on `Scheme`.

variable (X : Scheme.{u})

/-- Definition 28.15.4 (1): the number of branches of a scheme `X` at a point `x` is the number
of branches of the local ring `X.presheaf.stalk x`, computed from a chosen henselization `Ah`. -/
def branchNumberAt (x : X) (Ah : Type u) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] : ℕ∞ :=
  branchNumber (X.presheaf.stalk x) Ah

/-- The scheme-level branch number at `x` is the ring-level branch number of the stalk. -/
@[simp] theorem branchNumberAt_def (x : X) (Ah : Type u) [CommRing Ah]
    [Algebra (X.presheaf.stalk x) Ah] [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah = branchNumber (X.presheaf.stalk x) Ah :=
  rfl

/-- The branch number at `x` is the number of minimal primes of the chosen henselization. -/
@[simp] theorem branchNumberAt_eq_encard_minimalPrimes (x : X) (Ah : Type u) [CommRing Ah]
    [Algebra (X.presheaf.stalk x) Ah] [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah = (minimalPrimes Ah).encard :=
  rfl

/-- Definition 28.15.4 (2): the number of geometric branches of a scheme `X` at a point `x` is
the number of geometric branches of the local ring `X.presheaf.stalk x`, computed from a chosen
strict henselization `Ash`. -/
def geometricBranchNumberAt (x : X) (Ash : Type u) [CommRing Ash]
    [Algebra (X.presheaf.stalk x) Ash] [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] : ℕ∞ :=
  geometricBranchNumber (X.presheaf.stalk x) Ash

/-- The scheme-level geometric branch number at `x` is the ring-level geometric branch number of
the stalk. -/
@[simp] theorem geometricBranchNumberAt_def (x : X) (Ash : Type u) [CommRing Ash]
    [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash =
      geometricBranchNumber (X.presheaf.stalk x) Ash :=
  rfl

/-- The geometric branch number at `x` is the number of minimal primes of the chosen strict
henselization. -/
@[simp] theorem geometricBranchNumberAt_eq_encard_minimalPrimes (x : X) (Ash : Type u)
    [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash = (minimalPrimes Ash).encard :=
  rfl

end AlgebraicGeometry.Scheme
