import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

universe u v

variable {E : Type u} {R : Type v}
    [ConditionallyCompleteLattice R]
    [Semiring R] [IsOrderedRing R]
    [AddCommMonoid E] [Module R E]

open Function (verticalHeights)
open scoped Rockafellar

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.7 introduces the function attached to the cone from
  Definition 17.2.5 by taking its vertical infimum.
- `bridge/view`: the source-facing bridge `generated_cone_inf_eq_sInf` is stated in the
  intrinsic `verticalHeights` language.

Domain-style sampling used here:
- `K⋆[R]` from Definition 17.2.5;
- `Function.verticalHeights`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`.

Primitive data vs derived API:
- primitive source input: the cone owner `K⋆[R] SStar`.
- source-facing owner: `generated_cone_inf SStar`;
- derived bridge API: the intrinsic `verticalHeights` descriptions
  `generated_cone_inf_eq_sInf`.

Ambient minimization:
- this owner uses only the additive/module structure on `E` together with the vertical
  scalar coordinate already present in `K⋆[R] SStar`, so it is stated for arbitrary ordered
  scalar modules and later specialized to the textbook real layer.

Layer target: `source-facing`.
-/

/-- Definition 17.2.7: the function attached to `SStar` sends `x*` to the infimum of the scalar
heights `μ*` for which `(x*, μ*)` lies in `K⋆[R] SStar`. -/
def generated_cone_inf (SStar : Set EStar) : E → WithTopBot R :=
  Function.verticalInfimum (K⋆[R] SStar)

/-- Textbook-scoped notation for the Definition 17.2.7 owner. -/
scoped[Rockafellar] notation3:max "Kinf[" R "](" SStar ")" =>
  generated_cone_inf (R := R) SStar

/-- Canonical owner bridge from Definition 17.2.7 to Chapter 1's `verticalInfimum` owner. -/
@[simp] theorem generated_cone_inf_eq_verticalInfimum (SStar : Set EStar) :
    Kinf[R](SStar) = Function.verticalInfimum (K⋆[R] SStar) :=
  rfl

/-- Coercion-clean owner bridge: `generated_cone_inf SStar x*` is the infimum of the intrinsic
vertical heights above `x*` in `K⋆[R] SStar`. -/
theorem generated_cone_inf_eq_sInf (SStar : Set EStar) (xStar : E) :
    Kinf[R](SStar) xStar =
      sInf (verticalHeights (K⋆[R] SStar) xStar) := by
  simpa [generated_cone_inf] using
    Function.verticalInfimum_eq_sInf_verticalHeights
      (F := ((K⋆[R] SStar : PointedCone R EStar) : Set EStar)) xStar

end
