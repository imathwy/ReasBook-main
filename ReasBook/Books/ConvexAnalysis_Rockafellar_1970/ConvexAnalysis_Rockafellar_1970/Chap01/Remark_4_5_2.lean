import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped Rockafellar

attribute [local instance] Classical.propDecidable

section

variable {ι : Type*} [Fintype ι]

local notation "E" => (ι → ℝ)

/-
Source/core/bridge triage:
- `source-facing`: Remark 4.5.2 is the globally defined function that equals the negative
  geometric mean on the nonnegative orthant and `+∞` outside, for a finite coordinate family.
  The textbook statement is the specialization `ι = Fin n` with `n ≥ 1`.
- `core/canonical`: the chapter owner layer for such an extension is the ambient
  `WithBotTop ℝ`-valued function `Function.toWithBotTopOn` on the canonical set owner
  `orthant[ℝ](E)`.
- `bridge/view`: the source coordinatewise nonnegativity condition is the pointwise description of
  membership in `orthant[ℝ](E)`, and
  `Function.toWithBotTopOn_eq_add_indicator` /
  `isConvex_toWithBotTop_add_indicator_iff` are chapter bridges between the real branch
  and the ambient owner function.
- Primitive data vs derived API: the primitive datum is the real-valued branch
  `x ↦ - (∏ i, x i)^(1 / card ι)` on the ambient finite product; the global `WithBotTop ℝ`
  owner `negativeGeometricMean ι` and its pointwise formulas are derived owner-level API.
- Domain-style sampling used here: `Function.toWithBotTopOn`, `orthant[ℝ](E)`,
  `indicator`, the canonical owner identity
  `Function.toWithBotTopOn_eq_add_indicator`, and the convexity bridge
  `isConvex_toWithBotTop_add_indicator_iff`.
- Layer target: `source-facing`, but on the chapter's canonical ambient `WithBotTop ℝ` owner
  rather than through a separate `WithTop ℝ` wrapper.
- Ambient owner check: the carrier is the intrinsic finite product `ι → ℝ`; no Euclidean or
  inner-product model is required for this coordinatewise statement.
-/

/-- Real-valued finite branch of Remark 4.5.2.
The scalar layer is intrinsically `ℝ`: the geometric mean uses a generally nonintegral
exponent `1 / card ι`, whose canonical primitive owner in this project is `Real.rpow`. -/
def negativeGeometricMeanBranch : E → ℝ :=
  fun x ↦ -(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ)))

/-- Remark 4.5.2: for any finite coordinate family, the ambient extended-real-valued
function that equals the negative geometric mean on the nonnegative orthant and `+∞` outside it.
The textbook `R^n` function is the specialization `ι = Fin n` with `n ≥ 1`. -/
def negativeGeometricMean : E → WithBotTop ℝ :=
  Function.toWithBotTopOn negativeGeometricMeanBranch
    orthant[ℝ](E)

/-- Source-facing bridge form: `negativeGeometricMean` equals the branch plus the orthant
indicator. -/
theorem negativeGeometricMean_eq_add_indicator :
    negativeGeometricMean =
      negativeGeometricMeanBranch.toWithBotTop +
        (fun x : E ↦ δ[ℝ](x | orthant[ℝ](E))) := by
  simpa [negativeGeometricMean] using
    (Function.toWithBotTopOn_eq_add_indicator
      negativeGeometricMeanBranch
      (orthant[ℝ](E)))

/-- Outside the nonnegative orthant, `negativeGeometricMean` is `+∞`. -/
@[simp] theorem negativeGeometricMean_apply_of_not_mem_orthant {x : E}
    (hx : x ∉ orthant[ℝ](E)) :
    negativeGeometricMean x = ⊤ := by
  simpa [negativeGeometricMean] using
    (Function.toWithBotTopOn_of_notMem
      (f := negativeGeometricMeanBranch)
      (C := orthant[ℝ](E)) hx)

/-- On the nonnegative orthant, the ambient owner agrees with the real branch owner. -/
@[simp] theorem negativeGeometricMean_apply_of_mem_orthant_eq_branch {x : E}
    (hx : x ∈ orthant[ℝ](E)) :
    negativeGeometricMean x = negativeGeometricMeanBranch.toWithBotTop x := by
  simpa [negativeGeometricMean] using
    (Function.toWithBotTopOn_of_mem
      (f := negativeGeometricMeanBranch)
      (C := orthant[ℝ](E)) hx)

/-- On the nonnegative orthant, `negativeGeometricMean` is given by the negative
geometric-mean formula. -/
theorem negativeGeometricMean_apply_of_mem_orthant {x : E}
    (hx : x ∈ orthant[ℝ](E)) :
    negativeGeometricMean x =
      (-(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ))) : ℝ) := by
  simpa [negativeGeometricMeanBranch, Function.toWithBotTop] using
    (negativeGeometricMean_apply_of_mem_orthant_eq_branch (x := x) hx)

/-- Intrinsic-order view: `0 ≤ x` is exactly membership in `orthant[ℝ](E)`. -/
theorem negativeGeometricMean_apply_of_nonneg {x : E} (hx : (0 : E) ≤ x) :
    negativeGeometricMean x =
      (-(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ))) : ℝ) := by
  exact negativeGeometricMean_apply_of_mem_orthant <|
    (mem_orthant_iff).2 hx

/-- Coordinatewise bridge view of `negativeGeometricMean_apply_of_nonneg`. -/
theorem negativeGeometricMean_apply_of_coordwise_nonneg {x : E}
    (hx : ∀ i : ι, 0 ≤ x i) :
    negativeGeometricMean x =
      (-(Real.rpow (∏ i, x i) (1 / (Fintype.card ι : ℝ))) : ℝ) := by
  exact negativeGeometricMean_apply_of_nonneg (x := x) (by simpa using hx)

-- Proof sketch: rewrite the ambient function as the chapter owner
-- `Function.toWithBotTopOn negativeGeometricMeanBranch
-- (orthant[ℝ](E))`, equivalently the
-- bridge form from `negativeGeometricMean_eq_add_indicator`;
-- then apply the extension-by-`+∞`
-- bridge `isConvex_toWithBotTop_add_indicator_iff`, and prove convexity of the finite
-- branch on the nonnegative orthant by the Hessian argument from Theorem 4.5. The textbook
-- statement is the nonempty specialization `ι = Fin n` with `n ≥ 1`.
/-- Remark 4.5.2: the function that equals the negative geometric mean on the nonnegative orthant
and `+∞` otherwise is convex. -/
theorem negativeGeometricMean_isConvex :
    (negativeGeometricMean : E → WithBotTop ℝ).IsConvex ℝ := sorry

end
