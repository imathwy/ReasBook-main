import StacksProject_2024.Chap28.Definition_28_15_1
import StacksProject_2024.Chap28.Definition_28_15_4
import StacksProject_2024.Chap15.Lemma_15_107_3
import StacksProject_2024.Chap15.Lemma_15_107_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: the ring-level equivalences already live in Chapter 15, while Chapter 28 owns
-- the scheme-side stalkwise bridges `branchNumberAt`, `geometricBranchNumberAt`,
-- `Scheme.isUnibranchAt`, and `Scheme.isGeometricallyUnibranchAt`. This item should therefore be
-- stated on the scheme-level branch-number owners and proved by reduction to the stalk.

/-- Helper: a set has cardinality `1` exactly when it has a unique element. -/
lemma encard_eq_one_iff_existsUnique_mem {α : Type u} (s : Set α) :
    s.encard = 1 ↔ ∃! x, x ∈ s := by
  constructor
  · intro hs
    rcases Set.encard_eq_one.mp hs with ⟨x, rfl⟩
    refine ⟨x, by simp, ?_⟩
    intro y hy
    simpa using hy
  · rintro ⟨x, hx, huniq⟩
    have hs : s = ({x} : Set α) := by
      ext y
      constructor
      · intro hy
        exact huniq y hy
      · rintro rfl
        exact hx
    rw [hs, Set.encard_singleton]

variable {X : Scheme.{u}} (x : X)

/-- Lemma 28.15.6 (1): the branch number of a scheme `X` at a point `x`, computed from a chosen
henselization of the stalk `X.presheaf.stalk x`, is `1` if and only if `X` is unibranch at `x`.
-/
theorem branchNumberAt_eq_one_iff_isUnibranchAt
    (Ah : Type u) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
    [IsHenselizationOf (X.presheaf.stalk x) Ah] :
    X.branchNumberAt x Ah = 1 ↔ X.isUnibranchAt x := by
  rw [branchNumberAt_def, branchNumber, encard_eq_one_iff_existsUnique_mem]
  simpa [isUnibranchAt_iff] using
    (isUnibranch_iff_existsUnique_minimalPrime_henselization
      (A := X.presheaf.stalk x) (Ah := Ah)).symm

/-- Lemma 28.15.6 (2): the geometric branch number of a scheme `X` at a point `x`, computed from
a chosen strict henselization of the stalk `X.presheaf.stalk x`, is `1` if and only if `X` is
geometrically unibranch at `x`. -/
theorem geometricBranchNumberAt_eq_one_iff_isGeometricallyUnibranchAt
    (Ash : Type u) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
    [IsStrictHenselizationOf (X.presheaf.stalk x) Ash] :
    X.geometricBranchNumberAt x Ash = 1 ↔ X.isGeometricallyUnibranchAt x := by
  rw [geometricBranchNumberAt_def, geometricBranchNumber, encard_eq_one_iff_existsUnique_mem]
  simpa [isGeometricallyUnibranchAt_iff] using
    (isGeometricallyUnibranch_iff_existsUnique_minimalPrime_strictHenselization
      (A := X.presheaf.stalk x) (Ash := Ash)).symm

end AlgebraicGeometry.Scheme
