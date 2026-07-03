import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.MetricSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_15_0_37 (from Chap03) -/
noncomputable section

open scoped Pointwise

universe u

section

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the lemma compares the scaled perspectives `f_λ` and `g_μ`, where `g` is the
  obverse of `f`, under the standing Chapter 15 assumptions on `f`.
- `core/canonical`: the relevant owner declarations are the upstream Section 15 definitions
  `Function.rightScalarMul` and `obverse` from `Text_15_0_31`, together with the standing hypothesis
  package `Function.IsNonnegativeClosedConvexZero`.
- `bridge/view`: the relevant owner bridge is
  `obverse_epigraph_eq_one_sublevel_closedPerspective`, combined with the owner three-branch
  formula `lowerSemicontinuousHull_perspective_apply`, so no parallel wrapper notion is needed
  here.

Domain-style sampling used here:
- `rightScalarMul`;
- `obverse`;
- `lowerSemicontinuousHull_perspective_apply`;
- `obverse_epigraph_eq_one_sublevel_closedPerspective`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`.

Primitive data vs derived API:
- primitive inputs: the upstream Chapter 15 owner declarations `Function.rightScalarMul` and
  `obverse f`, together with the owner hypothesis package
  `f.IsNonnegativeClosedConvexZero`;
- derived API: the single comparison theorem between the `μ`-sublevel condition for `f_λ` and the
  `λ`-sublevel condition for `(obverse f)_μ`.

Layer target: `source-facing`, stated directly using the existing chapter owners.
Ambient minimization: the theorem uses only the Chapter 15 owner layer
`[TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]`; no coordinate model or inner-product
structure is part of the statement itself, and specializing to `EuclideanSpace ℝ (Fin n)` recovers
the textbook `R^n` presentation.
-/

-- Proof sketch: rewrite `(g_μ)(x) ≤ λ` as `g (μ⁻¹ • x) ≤ λ / μ` using the positive-scalar
-- evaluation formula for the positive right scalar multiple. Apply the owner bridge
-- `obverse_epigraph_eq_one_sublevel_closedPerspective` to the positive coordinate
-- `(λ / μ, μ⁻¹ • x)`, use `lowerSemicontinuousHull_perspective_apply` to replace the closed
-- perspective by the scaled perspective `f_(λ / μ) (μ⁻¹ • x)`, and then rewrite that perspective
-- back to
-- `λ * f (λ⁻¹ • x) ≤ μ`, i.e. `f_λ x ≤ μ`.
/-- Text 15.0.37: if `f : E → [0, +∞]` is convex, lower semicontinuous, and satisfies `f 0 = 0`,
then for positive scalars `λ` and `μ`, the inequality `(f_λ)(x) ≤ μ` holds if and only if the
corresponding inequality `(g_μ)(x) ≤ λ` holds for the obverse `g = obverse f`. Specializing
`E` to `EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem perspectiveScale_le_iff_obverse_perspectiveScale_le
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero)
    (lam mu : NNRealˣ) (x : E) :
    ((lam : NNReal) •ʳ f) x ≤ ((mu : ℝ) : EReal) ↔
      ((mu : NNReal) •ʳ obverse f) x ≤ ((lam : ℝ) : EReal) := sorry

end

/-! ### Text_15_0_38 (from Chap03) -/
noncomputable section

open scoped Pointwise

section

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the text identifies the `α`-sublevel set of the obverse `g = obverse f` with
  both the unit sublevel set of the scaled perspective `f_α` and the homothetic image
  `α • {x | f x ≤ α⁻¹}`.
- `core/canonical`: the owner API is the chapter-level source-facing trio
  `obverse`, `Function.rightScalarMul`, and the standing-hypothesis class
  `Function.IsNonnegativeClosedConvexZero`, imported upstream from `Text_15_0_31`.
- `bridge/view`: the first clause is now a direct specialization of the existing comparison
  theorem from `Text_15_0_37` at the unit scalar, under the standing Chapter 15 assumptions,
  while the second clause rewrites that unit sublevel set as a pointwise scalar multiple of an
  ordinary sublevel set of `f`.

Domain-style sampling used here:
- `obverse`;
- `rightScalarMul`;
- `perspectiveScale_le_iff_obverse_perspectiveScale_le`;
- `rightScalarMul_one`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `Set.mem_smul_set_iff_inv_smul_mem₀`.

Layer target: `source-facing`, split into the two atomic equalities displayed in the source.
Ambient minimization: the first statement uses the intrinsic Chapter 15 owner layer
`[TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]`, while the second only needs the scalar
action laws required by the positive right scalar multiple formula and the homothetic-set rewrite,
namely `[MulAction ℝ E]`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the source
presentation on `R^n`.
-/

-- Proof sketch: specialize the comparison theorem from `Text_15_0_37` to the unit scalar `μ = 1`.
-- The resulting right-hand side is the unit right scalar multiple of `obverse f` evaluated at
-- `x`, bounded by `α`, which reduces to
-- `obverse f x ≤ α` by the owner theorem `rightScalarMul_one`.
/-- Text 15.0.38 (1): for every positive scalar `α`, the `α`-sublevel set of the obverse
`g = obverse f` is exactly the unit sublevel set of the scaled perspective `f_α`, provided `f`
satisfies the standing Chapter 15 assumptions. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem obverse_sublevelSet_eq_perspectiveScale_unitSublevelSet
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) (α : NNRealˣ) :
    {x : E | obverse f x ≤ ((α : ℝ) : EReal)} =
      {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} := by
  ext x
  have hone : ((1 : NNReal) •ʳ obverse f) = obverse f :=
    (rightScalarMul_one (obverse f) : ((1 : NNReal) •ʳ obverse f) = obverse f)
  simpa [hone] using (perspectiveScale_le_iff_obverse_perspectiveScale_le f hf α 1 x).symm

end

section

variable {E : Type*} [MulAction ℝ E]

-- Proof sketch: unfold the positive right scalar multiple; the inequality
-- `α * f (α⁻¹ • x) ≤ 1` is equivalent to
-- `f (α⁻¹ • x) ≤ α⁻¹`. Writing `u = α⁻¹ • x` turns the unit sublevel set of `f_α` into the image
-- of `{u | f u ≤ α⁻¹}` under multiplication by `α`, i.e. into `α • {u | f u ≤ α⁻¹}`.
/-- Text 15.0.38 (2): for every positive scalar `α`, the unit sublevel set of the scaled
perspective `f_α` is the homothetic image by `α` of the `α⁻¹`-sublevel set of `f`. Specializing
`E` to `EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem perspectiveScale_unitSublevelSet_eq_smul_sublevelSet
    (f : E → EReal) (α : NNRealˣ) :
    {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} =
      (α : ℝ) • {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} := by
  ext x
  let f' : E → WithBotTop ℝ := f
  have hαreal : 0 < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hα : (0 : EReal) < (α : ℝ) := by
    exact_mod_cast (show 0 < (α : NNReal) from pos_iff_ne_zero.mpr (Units.ne_zero α))
  have hα0 : (α : ℝ) ≠ 0 := by
    exact_mod_cast (Units.ne_zero α)
  have hαTop : ((α : ℝ) : EReal) ≠ ⊤ := by
    simp
  have hαnn : (⟨(α : ℝ), hαreal.le⟩ : NNReal) = (α : NNReal) := by
    ext
    rfl
  have hright :
      ((⟨(α : ℝ), hαreal.le⟩ : NNReal) •ʳ f') x =
        (((α : ℝ) : WithBotTop ℝ)) * f' (((α : ℝ)⁻¹) • x) := by
    simpa [f'] using rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos f' hαreal x
  constructor <;> intro hx
  · exact
      (Set.mem_smul_set_iff_inv_smul_mem₀ hα0
        {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} x).2 <| by
      change ((α : NNReal) •ʳ f) x ≤ (1 : EReal) at hx
      rw [← hαnn] at hx
      change ((⟨(α : ℝ), hαreal.le⟩ : NNReal) •ʳ f') x ≤ (1 : WithBotTop ℝ) at hx
      rw [hright] at hx
      have hx' : f' (((α : ℝ)⁻¹) • x) * (((α : ℝ) : WithBotTop ℝ)) ≤ (1 : WithBotTop ℝ) := by
        rwa [f', mul_comm] at hx
      have hx'' :
          f' (((α : ℝ)⁻¹) • x) ≤
            (1 : WithBotTop ℝ) / (((α : ℝ) : WithBotTop ℝ)) :=
        (EReal.le_div_iff_mul_le hα hαTop).mpr hx'
      simpa [f', div_eq_mul_inv, EReal.coe_inv, mul_comm, mul_left_comm, mul_assoc] using hx''
  · have hx' :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ hα0
        {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} x).1 hx
    change ((α : NNReal) •ʳ f) x ≤ (1 : EReal)
    rw [← hαnn]
    change ((⟨(α : ℝ), hαreal.le⟩ : NNReal) •ʳ f') x ≤ (1 : WithBotTop ℝ)
    rw [hright]
    have hx'' :
        f' (((α : ℝ)⁻¹) • x) ≤
          (1 : WithBotTop ℝ) / (((α : ℝ) : WithBotTop ℝ)) := by
      simpa [f', div_eq_mul_inv, EReal.coe_inv, mul_comm, mul_left_comm, mul_assoc] using hx'
    have hx''' :
        f' (((α : ℝ)⁻¹) • x) * (((α : ℝ) : WithBotTop ℝ)) ≤ (1 : WithBotTop ℝ) :=
      (EReal.le_div_iff_mul_le hα hαTop).mp hx''
    rwa [f', mul_comm]

end

/-! ### Text_15_0_39 (from Chap03) -/
noncomputable section

open scoped ConvexFunctionPolar Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.39 states that for a nonnegative closed convex function `f` with
  `f 0 = 0`, the polar `fᵒ` is the obverse of the conjugate `f*`, and then records the resulting
  reciprocal-level sublevel-set identity.
- `core/canonical`: the owner declarations already present in the Chapter 15 API are
  the Chapter 15 polar owner `fᵒ`, `obverse`, `f⋆`, and
  `Function.IsNonnegativeClosedConvexZero`, together with the owner exchange theorem
  `obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero`.
- `bridge/view`: the main theorem below is the symmetric source-facing restatement of that owner
  exchange theorem, and the second sentence reuses the exact reciprocal-sublevel theorem from the
  preceding item instead of restating a parallel declaration.

Domain-style sampling used here:
- `Function.IsNonnegativeClosedConvexZero` as the owner hypothesis package for the standing
  nonnegative closed convex zero-normalized assumptions;
- `obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero` from the
  Section 15 owner API;
- the exact source-faithful reciprocal-sublevel theorem already present in `Text_15_0_36`.

Primitive data vs derived API:
- primitive input: a function `f : E → EReal` with owner hypothesis
  `f.IsNonnegativeClosedConvexZero`;
- derived API: the source-facing symmetric obverse identity and the recalled reciprocal-sublevel
  equality.

Layer target: the theorem is a thin `bridge/view` from the Section 15 owner theorem to the
source-facing wording of Text 15.0.39, while the sublevel-set identity is reused by direct recall.
-/

-- Proof sketch: Theorem 15.5 identifies `obverse fᵒ` with
-- `f⋆`, and the same theorem makes `obverse` involutive on the standing Chapter 15
-- class. Rewriting `fᵒ` as the double obverse of itself then gives the
-- symmetric source wording exactly.
/-- Text 15.0.39: if `f : E → [0, +∞]` is closed convex and satisfies `f 0 = 0` on a
finite-dimensional real inner-product space, then its polar `fᵒ` is the obverse of its Fenchel
conjugate `f*`, i.e. `fᵒ = obverse f⋆`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers
the source statement on `R^n`. -/
theorem convex_function_polar_eq_obverse_convexConjugate_of_nonnegative_closed_convex_zero
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    fᵒ = obverse f⋆ := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  refine (obverse_obverse_eq_of_nonnegative_closed_convex_zero
    fᵒ inferInstance).symm.trans ?_
  exact
    congrArg obverse
      (obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero
        f hf)

/- The reciprocal sublevel-set identity for the polar and Fenchel conjugate of a nonnegative
closed convex zero-normalized function is already available, with the exact statement shape used
here, from the preceding item. -/
recall polar_sublevelSet_eq_inv_smul_conjugate_sublevelSet_of_nonnegative_closed_convex_zero

end
