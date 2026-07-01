import Mathlib.Algebra.Ring.Action.Pointwise.Set
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_3_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

section

variable {𝕜 E : Type*} [Semifield 𝕜] [PartialOrder 𝕜]
  [AddLeftMono 𝕜] [PosMulReflectLT 𝕜]
  [AddCommMonoid E] [Module 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Text 3.2.2 states that for a convex set `C`, the Minkowski sum `C + C` equals
  the dilation `2C`.
- `core/canonical`: the owner abstraction is `Convex 𝕜 C`; the primitive upstream owner theorem is
  `Convex.add_smul_set`, specialized at `a = b = 1`.
- `bridge/view`: the textbook notation `2C` is Lean's pointwise scalar action `(2 : 𝕜) • C`, and
  `C + C` is the pointwise set sum.
- Primitive data vs derived API: the primitive data are convexity of `C` plus `0 ≤ (1 : 𝕜)`.
  `ZeroLEOneClass` is then a bridge-layer packaging of that primitive scalar fact.
- Domain-style sampling: this item aligns with `Convex.add_smul_set`, the convex-set owner
  `Convex`, and standard pointwise scalar-action notation.
- Ambient minimization: no additive inverses are used in `E`, so `[AddCommMonoid E]` is enough.
- Layer target: expose a primitive theorem at the explicit `0 ≤ 1` layer, then keep Text 3.2.2 as
  a thin typeclass bridge theorem.

Abstraction audit (canonicalize):
- Codomain/ambient over-concrete? `No`: this is set-valued and codomain-free.
- Scalar/ambient structure stronger than needed? `Improved`: the primitive theorem now requires
  only explicit `0 ≤ (1 : 𝕜)` instead of bundling that fact into a typeclass.
- Concrete-model owner leak? `No`: owner is intrinsic (`Convex`) and model-independent.
- Ambient-vs-intrinsic topology mismatch? `Not applicable`: no topological operator appears.
- Owner/name/notation surface canonical? `Yes`: the public theorem surface remains
  `C + C = (2 : 𝕜) • C` with standard pointwise notation.
-/

/-- Primitive owner form behind Text 3.2.2: convexity plus the scalar fact `0 ≤ 1` gives the
Minkowski-sum identity `C + C = (2 : 𝕜) • C`. -/
theorem Convex.add_self_eq_two_smul {C : Set E} (hC : Convex 𝕜 C)
    (h01 : (0 : 𝕜) ≤ 1) :
    C + C = (2 : 𝕜) • C := by
  simpa [one_add_one_eq_two] using
    (hC.add_smul_set (1 : 𝕜) (1 : 𝕜) h01 h01).symm

section

variable [ZeroLEOneClass 𝕜]

/-- Text 3.2.2 bridge form: for a convex set `C`, the Minkowski sum `C + C` equals `(2 : 𝕜) • C`.
This packages the primitive scalar side-condition `0 ≤ (1 : 𝕜)` via `ZeroLEOneClass`. -/
theorem Convex.add_self_eq_two_smul_of_zeroLEOneClass {C : Set E} (hC : Convex 𝕜 C) :
    C + C = (2 : 𝕜) • C := by
  exact hC.add_self_eq_two_smul (h01 := (show (0 : 𝕜) ≤ 1 from zero_le_one))

end

end
