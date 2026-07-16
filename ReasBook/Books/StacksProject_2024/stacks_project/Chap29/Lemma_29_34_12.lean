import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_14_1
import StacksProject_2024.stacks_project.Chap17.Definition_17_28_10
import StacksProject_2024.stacks_project.Chap29.Lemma_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the canonical smoothness owners `Smooth`,
  `SmoothOfRelativeDimension`, and the affine cotangent-rank theorem
  `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`;
- local Chapter 17/29 precedent already fixes the source-facing scheme API as `Ω[f.toShHom]` for
  relative differentials, `SheafOfModules.IsFiniteLocallyFree` for finite local freeness of module
  sheaves, and `Scheme.Hom.fiberDimensionAt` for the fibre dimension at a point.
-/

universe u

variable {X S : Scheme.{u}}

/-- Smoothness canonically makes the sheaf of relative differentials finite locally free. -/
instance smooth_differentials_isFiniteLocallyFree
    (f : X ⟶ S) [Smooth f] :
    (Ω[f.toShHom]).IsFiniteLocallyFree := by
  sorry

/-- Lemma 29.34.12 (1): if `f : X ⟶ S` is smooth, then the module of differentials
`\Omega_{X/S}` is finite locally free. -/
@[stacks 02G1]
theorem isFiniteLocallyFree_differentials_of_smooth
    (f : X ⟶ S) (hf : Smooth f) :
    (Ω[f.toShHom]).IsFiniteLocallyFree := by
  letI : Smooth f := hf
  infer_instance

/-- Lemma 29.34.12 (2): if `f : X ⟶ S` is smooth, then for every `x : X` the rank of the stalk of
`\Omega_{X/S}` at the closed point of `\operatorname{Spec}(\mathcal O_{X,x})` equals the local
dimension of the fibre of `f` at `x`. -/
@[stacks 02G1]
theorem rankAtClosedPoint_differentials_eq_fiberDimensionAt_of_smooth
    (f : X ⟶ S) (hf : Smooth f) (x : X) :
    (Module.rankAtStalk
      (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)
      (IsLocalRing.closedPoint (X.presheaf.stalk x)) : WithBot ℕ∞) =
      f.fiberDimensionAt x := sorry

end AlgebraicGeometry
