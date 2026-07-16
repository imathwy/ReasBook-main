import StacksProject_2024.stacks_project.Chap05.Definition_5_10_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open AlgebraicGeometry

section

variable {X S : Scheme} (f : X ⟶ S)

namespace Scheme.Hom

/-- The canonical algebra structure on residue fields induced by a morphism of schemes at a point. -/
local instance residueFieldAlgebraAtPoint (x : X) :
    Algebra (S.residueField (f x)) (X.residueField x) :=
  (f.residueFieldMap x).hom.toAlgebra

local notation "fiberStalkAt" =>
  fun x : X ↦ (f.fiber (f x)).presheaf.stalk (f.asFiber x)

local notation "residueFieldTrdegAt" =>
  fun x : X ↦ Cardinal.toNat (Algebra.trdeg (S.residueField (f x)) (X.residueField x))

/- Semantic recall / owner check:
- local Chapter 29 precedent represents the source quantity `dim_x(X_{f(x)})` by the owner
  `Scheme.Hom.fiberDimensionAt`;
- the point `x` viewed on the fibre over `f x` is `f.asFiber x`, so
  `topologicalKrullDimAt (f.asFiber x)` is the companion topological view of the same local
  dimension.
-/

/-- The canonical fiber-dimension owner agrees with the local topological Krull dimension at the
corresponding point of the scheme-theoretic fiber. -/
theorem fiberDimensionAt_eq_topologicalKrullDimAt_asFiber (x : X) :
    f.fiberDimensionAt x = topologicalKrullDimAt (f.asFiber x) := sorry

/-- Lemma 29.28.1 in owner form: the chapter's canonical fiber-dimension owner satisfies the local
dimension formula for locally finite type morphisms. -/
theorem fiberDimensionAt_eq_ringKrullDim_stalk_add_trdeg_residueField
    [LocallyOfFiniteType f] (x : X) :
    f.fiberDimensionAt x = ringKrullDim (fiberStalkAt x) + residueFieldTrdegAt x := sorry

/-- Lemma 29.28.1: if `f : X ⟶ S` is locally of finite type and `x : X`, then the local dimension
of the fiber `X_s` at the corresponding point `x` equals the Krull dimension of the local ring
`𝒪_{X_s, x}` plus the transcendence degree of `κ(x)` over `κ(s)`, where `s = f x`. This is the
topological-fiber view of the canonical owner formula
`fiberDimensionAt_eq_ringKrullDim_stalk_add_trdeg_residueField`. -/
@[stacks 02FW]
theorem topologicalKrullDimAt_asFiber_eq_ringKrullDim_stalk_add_trdeg_residueField
    [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt (f.asFiber x) = ringKrullDim (fiberStalkAt x) + residueFieldTrdegAt x :=
  sorry

end Scheme.Hom

end
