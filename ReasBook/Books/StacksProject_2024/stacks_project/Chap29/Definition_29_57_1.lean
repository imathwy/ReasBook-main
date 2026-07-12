import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.Finite

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

variable {X Y : Scheme.{u}}

-- Semantic recall: mathlib already provides the canonical fibre owners `Scheme.Hom.fiber` and
-- `Scheme.Hom.fiberToSpecResidueField`, together with the finite-morphism owner
-- `AlgebraicGeometry.IsFinite`. The source-facing predicate should therefore reuse those owners
-- directly rather than re-spelling the fibre as a raw pullback.

/-- The global sections of the fibre of `f` over `y`. -/
abbrev fiberGlobalSections (f : X ⟶ Y) (y : Y) :=
  Scheme.Γ.obj (Opposite.op (f.fiber y))

/-- The canonical `κ(y)`-algebra structure on the global sections of the fibre of `f` over `y`. -/
@[reducible] instance fiberGlobalSectionsAlgebra (f : X ⟶ Y) (y : Y) :
    Algebra (Y.residueField y) (fiberGlobalSections f y) :=
  (CommRingCat.Hom.hom
      ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        appTop (f.fiberToSpecResidueField y))).toAlgebra

/-- The degree of the fibre of `f` over `y` as a `κ(y)`-algebra. -/
abbrev fiberDegree (f : X ⟶ Y) (y : Y) : ℕ :=
  Module.finrank (Y.residueField y) (fiberGlobalSections f y)

/-- Definition 29.57.1 (1): a natural number `n` bounds the degrees of the fibres of `f` if,
for every `y : Y`, the fibre `X_y` is finite over `κ(y)` and has degree at most `n` over
`κ(y)`. -/
@[stacks 03J4]
def degreesOfFibresBoundedBy (f : X ⟶ Y) (n : ℕ) : Prop :=
  ∀ y : Y,
    IsFinite (f.fiberToSpecResidueField y) ∧
      f.fiberDegree y ≤ n

@[stacks 03J4]
theorem degreesOfFibresBoundedBy.isFinite {f : X ⟶ Y} {n : ℕ}
    (h : degreesOfFibresBoundedBy f n) (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) :=
  (h y).1

@[stacks 03J4]
theorem degreesOfFibresBoundedBy.fiberDegree_le {f : X ⟶ Y} {n : ℕ}
    (h : degreesOfFibresBoundedBy f n) (y : Y) :
    f.fiberDegree y ≤ n :=
  (h y).2

/-- Definition 29.57.1 (2): the fibres of `f` are universally bounded if there exists a uniform
natural-number bound on the degrees of all fibres. -/
@[stacks 03J4]
def universallyBoundedFibres (f : X ⟶ Y) : Prop :=
  ∃ n : ℕ, degreesOfFibresBoundedBy f n

end Scheme.Hom
end AlgebraicGeometry
