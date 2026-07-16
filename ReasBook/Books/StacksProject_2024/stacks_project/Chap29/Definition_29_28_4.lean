import StacksProject_2024.stacks_project.Chap10.Definition_10_125_1

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X S : Scheme.{u}}

/-- The local dimension of the fiber of `f` at the point `x`. -/
noncomputable def fiberDimensionAt (f : X ⟶ S) (x : X) : WithBot ℕ∞ :=
  let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  relativeDimensionAt (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
    (IsLocalRing.closedPoint (X.presheaf.stalk x))

/-- `fiberDimensionAt` is the ring-level relative dimension of the stalk map at the closed point of
`Spec 𝒪_{X,x}`. -/
theorem fiberDimensionAt_eq_relativeDimensionAt (f : X ⟶ S) (x : X) :
    f.fiberDimensionAt x =
      let _ : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
      relativeDimensionAt (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (IsLocalRing.closedPoint (X.presheaf.stalk x)) :=
  rfl

/-- The locus of points where the fiber of `f` has local dimension at most `n`. -/
noncomputable def fiberDimensionLELocus (f : X ⟶ S) (n : ℕ) : Set X :=
  { x | f.fiberDimensionAt x ≤ (n : WithBot ℕ∞) }

/-- Membership in `fiberDimensionLELocus` means that the local ring of the fiber over `f(x)` at the
closed point of `Spec 𝒪_{X,x}` has Krull dimension at most `n`. -/
theorem mem_fiberDimensionLELocus (f : X ⟶ S) (n : ℕ) (x : X) :
    x ∈ f.fiberDimensionLELocus n ↔ f.fiberDimensionAt x ≤ (n : WithBot ℕ∞) :=
  Iff.rfl

end Scheme.Hom

end AlgebraicGeometry
