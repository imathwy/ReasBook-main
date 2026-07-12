import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_6_30_11

noncomputable section

open scoped Rockafellar

universe u v u' v'

namespace Bifunction

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 6.30.12 says that if `(P)` is the convex program attached to a closed
  proper convex bifunction `F`, then taking the dual program twice returns the original program.
  dual bifunction, the explicit iterated owner `adjoint U X (adjoint XStar UStar F)` for `F⋆⋆`,
  and `objective` for
  the zero-slice objective of the program attached to a bifunction, and
  `biadjointFunction_eq_closure` for double adjunction.
- `bridge/view`: the project does not package programs as separate structures; instead, the
  source program `(P)` is represented by `objective F`, and the dual of `(P*)` is represented by
  the zero-slice objective of the iterated adjoint bifunction
  `((adjoint U X (adjoint XStar UStar F))₀)`.

Domain-style sampling used here:
- `objective` from `Definition_6_29_12`;
- `adjoint` from `Definition_6_30_14`;
- `biadjointFunction_eq_closure` from `Theorem_6_30_11`.

Primitive data vs derived API:
- primitive input: a bifunction `F : U → X → WithBotTop 𝕜`;
- primitive owner expressions already upstream: `(F)₀` and
  `adjoint U X (adjoint XStar UStar F)`;
- derived API added here: the source-facing identification of the dual of the dual program with
  the original program.

Redundant-source-assumption elimination:
- the source includes properness, but the program-level involutivity only uses the double-adjoint
  closure formula together with closedness of `Function.uncurry F`; properness does not change the
  mathematical content of this item's canonical owner statement.

Layer target: `bridge/view`, stated on the chapter's existing program owners rather than on a new
wrapper for convex or dual programs.
-/

section

variable {𝕜 : Type*} {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology 𝕜]
variable [TopologicalSpace U] [AddCommGroup U] [Module 𝕜 U]
variable [IsTopologicalAddGroup U] [ContinuousSMul 𝕜 U] [FiniteDimensional 𝕜 U] [T2Space U]
variable [TopologicalSpace X] [AddCommGroup X] [Module 𝕜 X]
variable [IsTopologicalAddGroup X] [ContinuousSMul 𝕜 X] [FiniteDimensional 𝕜 X] [T2Space X]
variable [TopologicalSpace UStar] [AddCommGroup UStar] [Module 𝕜 UStar]
variable [IsTopologicalAddGroup UStar] [ContinuousSMul 𝕜 UStar]
variable [FiniteDimensional 𝕜 UStar] [T2Space UStar]
variable [TopologicalSpace XStar] [AddCommGroup XStar] [Module 𝕜 XStar]
variable [IsTopologicalAddGroup XStar] [ContinuousSMul 𝕜 XStar]
variable [FiniteDimensional 𝕜 XStar] [T2Space XStar]
variable [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]

variable (F : U → X → WithBotTop 𝕜)

local instance : HasPairing XStar X 𝕜 :=
  HasPairing.swap (X := X) (Y := XStar) (L := 𝕜)

local instance : HasPairing UStar U 𝕜 :=
  HasPairing.swap (X := U) (Y := UStar) (L := 𝕜)

local notation "F⋆" => (adjoint XStar UStar F)
local notation "F⋆⋆" => (adjoint U X F⋆)

-- Proof sketch: the lower-semicontinuity hypothesis gives the canonical closure fixed-point
-- identity `cl F = F` on the graph function. Feed that into the existing Chapter 6 owner theorem
-- `biadjointFunction_eq_self_of_closure_eq_self`, then apply the zero-slice owner `objective`.
/-- Theorem 6.30.12: if `F` is a closed convex bifunction, then the dual of the dual program
attached to `F` is the original program, rendered canonically as equality between the zero-slice
objective of the iterated adjoint bifunction and the original zero-slice objective
`objective F`. -/
theorem objective_biadjointFunction_eq_objective
    (hF_convex : (Function.uncurry F).IsConvex 𝕜)
    (hF_closed : LowerSemicontinuous (Function.uncurry F)) :
    (F⋆⋆)₀ = (F)₀ := by
  have hF_closure : cl F = F := by
    ext u x
    exact congrArg (fun g ↦ g (u, x)) (lowerSemicontinuousHull_eq_self hF_closed)
  simpa [objective] using congrArg objective
    (biadjointFunction_eq_self_of_closure_eq_self (F := F) hF_convex hF_closure)

end

end Bifunction
