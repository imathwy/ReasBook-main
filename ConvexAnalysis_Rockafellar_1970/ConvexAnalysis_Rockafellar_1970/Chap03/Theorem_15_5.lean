import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_14_7
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexFunctionPolar RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 15.5 says that on the Chapter 15 class of nonnegative closed convex
  functions on a finite-dimensional real inner-product space with value `0` at the origin, the
  obverse operation is involutive and exchanges the polar with the Fenchel conjugate.
- `core/canonical`: the owner abstraction is `Function.IsNonnegativeClosedConvexZero`, and the
  core constructions already present upstream are `obverse`, the Chapter 15 polar owner `fᵒ`,
  `f⋆`, the bridge theorem
  `convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero`, and the
  Chapter 15 polar-owner instance `instIsNonnegativeClosedConvexZeroConvexFunctionPolar`.
- `bridge/view`: the exchange formulas below remain source-facing equalities between the three
  owner constructions. The stability of the Chapter 15 class under `obverse` is best exposed at
  the owner layer as instances rather than as parallel theorems returning the class predicate.

Domain-style sampling used here:
- `Function.IsNonnegativeClosedConvexZero`;
- `obverse`;
- `convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero`;
- `instIsNonnegativeClosedConvexZeroConvexFunctionPolar`.

Primitive data vs derived API:
- primitive input: a function `f : E → EReal` with the owner hypothesis
  `f.IsNonnegativeClosedConvexZero`;
- derived API: the induced owner instances on `f⋆` and `obverse f`, the involutivity identity
  `obverse (obverse f) = f`, and the two exchange identities `(obverse f)⋆ = fᵒ`,
  `obverse fᵒ = f⋆`, and `(obverse f)ᵒ = f⋆`.

Layer target: the equalities remain `source-facing`, while the class-preservation clause is
refined to the `core/canonical` owner layer.
-/

variable (f : E → EReal)

instance instIsNonnegativeClosedConvexZeroConvexConjugate
    (f : E → EReal) [hf : f.IsNonnegativeClosedConvexZero] :
    (f⋆ : E → EReal).IsNonnegativeClosedConvexZero := by
  have hconj : (f⋆ : E → EReal).IsClosedProperConvex :=
    hf.isClosedProperConvex.convexConjugate
  exact
    { convex := hconj.convex
      closed := hconj.closed
      nonneg := convexConjugate_nonneg_of_map_zero f hf.map_zero
      map_zero := convexConjugate_zero_of_nonneg_map_zero f hf.nonneg hf.map_zero }

-- Proof sketch: combine the pointwise identity `obverse f = convex_function_polar f⋆`
-- from Text 15.0.31 with the closedness, convexity, nonnegativity, and origin-normalization facts
-- for `f⋆`. Theorem 15.4 then applies to `f⋆`, and the resulting
-- bipolar identity simplifies via closed-convex Fenchel biconjugacy to show that `obverse f`
-- again lies in the same class.
/-- Theorem 15.5 first closes the Chapter 15 owner class under `obverse`. -/
instance instIsNonnegativeClosedConvexZeroObverse
    (f : E → EReal) [hf : f.IsNonnegativeClosedConvexZero] :
    (obverse f).IsNonnegativeClosedConvexZero := by
  letI : (f⋆ : E → EReal).IsNonnegativeClosedConvexZero :=
    instIsNonnegativeClosedConvexZeroConvexConjugate f
  have hobverse : obverse f = (f⋆)ᵒ := by
    ext x
    symm
    exact
      convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero f hf x
  exact
    hobverse.symm ▸
      (inferInstance : (f⋆)ᵒ.IsNonnegativeClosedConvexZero)

-- Proof sketch: write `g = obverse f`. Theorem 15.5 gives `f = obverse g`, so Text 15.0.31
-- applied to `g` identifies `(g⋆)ᵒ` with `f`. Substituting
-- `g = obverse f` and comparing with the Chapter 15 polar owner yields `g⋆ = fᵒ`.
/-- The Fenchel conjugate of the obverse `g = obverse f` is the polar `fᵒ`. -/
theorem convexConjugate_obverse_eq_convex_function_polar_of_nonnegative_closed_convex_zero
    (hf : f.IsNonnegativeClosedConvexZero) :
    ((obverse f)⋆ : E → EReal) = fᵒ := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : (obverse f).IsNonnegativeClosedConvexZero := inferInstance
  sorry

/-- Theorem 15.5: if `g = obverse f` for a nonnegative lower semicontinuous convex function `f`
with `f 0 = 0`, then the obverse of `g` is `f`; equivalently, the obverse construction is
symmetric on this class of functions. -/
theorem obverse_obverse_eq_of_nonnegative_closed_convex_zero
    (hf : f.IsNonnegativeClosedConvexZero) :
    obverse (obverse f) = f := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : (obverse f).IsNonnegativeClosedConvexZero := inferInstance
  ext x
  calc
    obverse (obverse f) x = ((obverse f)⋆)ᵒ x := by
      symm
      exact
        convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero
          (obverse f) inferInstance x
    _ = fᵒᵒ x := by
      rw [convexConjugate_obverse_eq_convex_function_polar_of_nonnegative_closed_convex_zero f hf]
    _ = f x := by
      simpa using congrFun (convex_function_polar_involutive f hf) x

-- Proof sketch: apply Theorem 12.2 to the closed convex function `obverse fᵒ`.
-- Its conjugate is `fᵒᵒ`, which collapses to `f` by
-- the owner involution from Theorem 15.4, so the biconjugate identity identifies
-- `obverse fᵒ` itself with `f*`.
/-- The polar `fᵒ` and the Fenchel conjugate `f*` are obverses of one another. -/
theorem obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero
    (hf : f.IsNonnegativeClosedConvexZero) :
    obverse fᵒ = f⋆ := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : fᵒ.IsNonnegativeClosedConvexZero := inferInstance
  have hobverseClass :
      (obverse fᵒ).IsNonnegativeClosedConvexZero := inferInstance
  have hobverse :
      (obverse fᵒ).IsClosedProperConvex :=
    hobverseClass.isClosedProperConvex
  have hconj : (obverse fᵒ)⋆ = f := by
    calc
      (obverse fᵒ)⋆ = ((fᵒ)ᵒ : E → EReal) :=
        convexConjugate_obverse_eq_convex_function_polar_of_nonnegative_closed_convex_zero
          fᵒ inferInstance
      _ = f := convex_function_polar_involutive f hf
  calc
    obverse fᵒ = (obverse fᵒ)⋆⋆ := by
      symm
      exact hobverse.biconjugate_eq
    _ = f⋆ := by
      simpa using congrArg (fun g ↦ g⋆) hconj

-- Proof sketch: write `obverse f = (f⋆)ᵒ` by Text 15.0.31 and then apply the bipolar involution
-- to `f⋆`.
/-- The polar of the obverse `g = obverse f` is the Fenchel conjugate `f*`. -/
theorem convex_function_polar_obverse_eq_convexConjugate_of_nonnegative_closed_convex_zero
    (hf : f.IsNonnegativeClosedConvexZero) :
    (obverse f)ᵒ = f⋆ := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : (f⋆ : E → EReal).IsNonnegativeClosedConvexZero :=
    instIsNonnegativeClosedConvexZeroConvexConjugate f
  have hobverse : obverse f = (f⋆)ᵒ := by
    ext x
    symm
    exact
      convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero f hf x
  rw [hobverse]
  exact convex_function_polar_involutive f⋆ inferInstance

end
