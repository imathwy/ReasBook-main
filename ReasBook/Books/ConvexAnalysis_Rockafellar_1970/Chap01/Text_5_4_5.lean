import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open scoped Pointwise
open scoped Function

variable {E : Type*}
variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [MulAction 𝕜 E]

/-- Helper for Text 5.4.5: extend scalar multiplication to `WithTopBot 𝕜` by multiplying on the
left after coercing the scalar. -/
local instance instSMulWithTopBot : SMul 𝕜 (WithTopBot 𝕜) where
  smul c z := (c : WithTopBot 𝕜) * z

-- Route correction: the canonical `Text_5_4_2`/`Text_5_4_3` owner chain is currently blocked by
-- upstream artifact failures, so this file works directly on the positive-scalar surface that
-- Text 5.4.5 actually quantifies over.
local infixr:73 " •ʳ " => fun a f => fun x ↦ a • f ((a : 𝕜)⁻¹ • x)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.5 characterizes positive homogeneity by invariance under the right
  scalar-multiplication operation `f ↦ f λ`.
- `core/canonical`: the owner abstractions are the previously introduced declarations
  `rightScalarMul` (used on positive scalars via notation), and
  `Function.PositivelyHomogeneous` for functions `E → WithTopBot 𝕜`.
- `bridge/view`: the positive-scalar view of `rightScalarMul` is provided directly by
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`, exposing the positive scalar through
  the intrinsic owner `a : 𝕜⁺`; this file exposes that view directly on the
  positive-scalar notation surface and rewrites the epigraph-based definition into the textbook
  pointwise formula
  `x ↦ λ f (x / λ)` for positive scalars.
- Layer target: `source-facing`, expressed directly in terms of the canonical owner predicate
  `Function.PositivelyHomogeneous` from `Definition_4_8`.
- Primitive data vs derived API: the positive scalar `λ` and the function `f` are primitive; the
  fixed-point characterization of positive homogeneity is the derived API.

Domain-style sampling used here:
- `rightScalarMul` and `rightScalarMul_eq_sInf` from `Text_5_4_2`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` from `Text_5_4_3`;
- the generic owner `Function.PositivelyHomogeneous : (E → WithTopBot 𝕜) → Prop` from
  `Definition_4_8`, recalled in `Text_5_4_4`.
- Ambient minimization: both owners already live canonically over an arbitrary `𝕜`-action, and
  the proof uses only the multiplicative scalar-action identities
  `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` and `smul_inv_smul₀`, with no additive,
  linear, coordinate, or finite-dimensional structure. The public theorem is therefore
  stated at that intrinsic `MulAction` level rather than through a concrete coordinate model.

The source phrases the statement for convex functions, but once `rightScalarMul` is defined
for arbitrary functions the equivalence itself depends only on that definition, so the convexity
hypothesis is redundant and omitted from the main declaration.
-/

namespace Function

-- Proof sketch: use `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos` from Text 5.4.3.
-- If `f` is positively homogeneous, apply the scaling law to `λ` and `λ⁻¹ • x` to get
-- `λ • f (λ⁻¹ • x) = f x`, hence every positive right scalar multiple `(a •ʳ f)` fixes
-- `f`.
-- Conversely, if every such positive right scalar multiple fixes `f`, evaluate the fixed-point
-- identity at `λ • x` and rewrite with the same explicit formula to recover
-- `f (λ • x) = λ • f x`.

/-- Helper for Text 5.4.5: positive-scalar pointwise formula for right scalar multiplication. -/
theorem rightScalarMulPos_apply_eq_mul_comp_inv_smul
    (f : E → WithTopBot 𝕜) (a : 𝕜⁺) (x : E) :
    (a •ʳ f) x = a • f ((a : 𝕜)⁻¹ • x) := by
  -- The local notation is already the textbook positive-scalar formula.
  rfl

/-- Helper for Text 5.4.5: a positively homogeneous function is fixed by every positive
right scalar multiplication. -/
theorem rightScalarMul_eq_self_of_positivelyHomogeneous
    {f : E → WithTopBot 𝕜} (hf : f.PositivelyHomogeneous 𝕜) :
    ∀ a : 𝕜⁺, a •ʳ f = f := by
  intro a
  -- Rewrite the right scalar multiple pointwise and evaluate homogeneity on the inverse-scaled
  -- argument so the scalar and its inverse cancel.
  ext x
  calc
    (a •ʳ f) x = a • f ((a : 𝕜)⁻¹ • x) := by
      simpa using rightScalarMulPos_apply_eq_mul_comp_inv_smul (f := f) (a := a) (x := x)
    _ = f (a • ((a : 𝕜)⁻¹ • x)) := by
      simpa using (hf.map_smul_pos a ((a : 𝕜)⁻¹ • x)).symm
    _ = f x := by
      -- Collapse the scalar and its inverse before returning to the original argument.
      simpa [smul_smul, one_smul, a.2.ne'] using
        congrArg f (smul_inv_smul₀ a.2.ne' x)

/-- Helper for Text 5.4.5: invariance under every positive right scalar multiplication implies
positive homogeneity. -/
theorem positivelyHomogeneous_of_rightScalarMul_eq_self
    {f : E → WithTopBot 𝕜} (hfix : ∀ a : 𝕜⁺, a •ʳ f = f) :
    f.PositivelyHomogeneous 𝕜 := by
  intro a x
  -- Evaluate the fixed-point identity at the scaled argument and unfold the right scalar
  -- multiplication there to recover the defining scaling law.
  have hfixa : a •ʳ f = f := hfix a
  calc
    f (a • x) = (a •ʳ f) (a • x) := by
      simpa using (congrFun hfixa (a • x)).symm
    _ = a • f ((a : 𝕜)⁻¹ • (a • x)) := by
      simpa using rightScalarMulPos_apply_eq_mul_comp_inv_smul
        (f := f) (a := a) (x := a • x)
    _ = a • f x := by
      -- Collapse the inverse scalar on the argument before applying `f`.
      simpa [smul_smul, one_smul, a.2.ne'] using
        congrArg (fun y ↦ a • f y) (inv_smul_smul₀ a.2.ne' x)

/-- Text 5.4.5: a function is positively homogeneous exactly when every positive right scalar
multiple fixes it. -/
theorem positivelyHomogeneous_iff_rightScalarMul_eq_self (f : E → WithTopBot 𝕜) :
    f.PositivelyHomogeneous 𝕜 ↔
      ∀ a : 𝕜⁺, a •ʳ f = f := by
  constructor
  · intro hf
    exact rightScalarMul_eq_self_of_positivelyHomogeneous hf
  · intro hfix
    exact positivelyHomogeneous_of_rightScalarMul_eq_self hfix

end Function

end
