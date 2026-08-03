import BauschkeLean.Chap01.Text_1_0_13
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap09.Proposition_9_5
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Corollary_12_19
import BauschkeLean.Chap13.Definition_13_1
import BauschkeLean.Chap16.Proposition_16_27
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Corollary_16_41
import BauschkeLean.Chap20.Example_20_3
import BauschkeLean.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open scoped InnerProductSpace

universe u

namespace SetValuedOperator

noncomputable section

/- Source/core/bridge triage:
- `source-facing`: Proposition 20.40 defines the quadratic potential on a subspace and the
  associated supremal potential attached to a symmetric monotone linear map.
- `core/canonical`: the ambient owner abstractions are `ofFunction`, `IsMonotone`,
  `Maximal IsMonotone`, `Γ₀(H)`, `∂`, and the canonical extension-by-`⊤` owner
  `ERealFunction.extendWithTopOutside`.
- `bridge/view`: `domainQuadraticPotential` remains the source-facing potential, but its concrete
  extension-off-the-domain implementation is now delegated to the canonical Chapter 12 owner.
- Primitive data: `D : Submodule ℝ H` and `T : D →ₗ[ℝ] H`.
- Derived API: `ofFunction D T`, `domainQuadraticPotential D T`, and
  `supremalPotential D T`. -/
-- Semantic recall: `lean_leansearch` did not expose a direct canonical owner for this proposition,
-- so the source-facing potential owners remain the public interface here.

section Potentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The affine defect `⟪x, T y⟫_ℝ - (1 / 2) ⟪y, T y⟫_ℝ` used in the supremum defining
`supremalPotential D T`. -/
private def affineDefect {D : Submodule ℝ H} (T : D →ₗ[ℝ] H) (x : H) (y : D) : EReal :=
  (((⟪x, T y⟫_ℝ - (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) : ℝ) : EReal)

-- Proof sketch: evaluate the `y = 0` term in the defining supremum; since `0 : D`, the supremum
-- is bounded below by the real value `0`, hence it is strictly above `⊥`.
/-- The supremum defining `supremalPotential D T` always lies in `]-∞,+∞]`. -/
private theorem supremalPotential_mem_Ioi
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) (x : H) :
    (⊥ : EReal) < ⨆ y : D, affineDefect T x y := by
  -- The branch indexed by `0 : D` already gives the finite value `0`.
  have hzero_branch : affineDefect T x 0 = (0 : EReal) := by
    simp [affineDefect]
  have hzero_le : (0 : EReal) ≤ ⨆ y : D, affineDefect T x y := by
    rw [← hzero_branch]
    exact le_iSup (fun y : D ↦ affineDefect T x y) 0
  -- Since `⊥ < 0`, the whole supremum stays strictly above `⊥`.
  exact lt_of_lt_of_le (by simp) hzero_le

/-- The function `h` from Proposition 20.40, attached to a linear map `T` defined on a subspace
`D`, equal to `(1 / 2) ⟪x, T x⟫_ℝ` on `D` and `+∞` off `D`. -/
noncomputable def domainQuadraticPotential
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) : H → Set.Ioi (⊥ : EReal) :=
  extendWithTopOutside D (fun x ↦ (1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ)

-- Proof sketch: unfold `domainQuadraticPotential`; on `D` the definition takes the finite
-- quadratic value associated with `T`.
/-- On the subspace `D`, `domainQuadraticPotential D T` equals `(1 / 2) ⟪x, T x⟫_ℝ`. -/
@[simp] theorem domainQuadraticPotential_apply_of_mem
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) {x : H} (hx : x ∈ D) :
    (domainQuadraticPotential D T x : EReal) =
      (((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ) : EReal) := by
  -- On the domain, `extendWithTopOutside` reduces to the original quadratic formula.
  simpa [domainQuadraticPotential] using
    (ERealFunction.extendWithTopOutside_apply_of_mem
      (h := fun y : D ↦ (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) hx)

-- Proof sketch: unfold `domainQuadraticPotential`; off `D` the definition is the constant value
-- `⊤`.
/-- Outside the subspace `D`, `domainQuadraticPotential D T` equals `+∞`. -/
@[simp] theorem domainQuadraticPotential_apply_of_not_mem
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) {x : H} (hx : x ∉ D) :
    (domainQuadraticPotential D T x : EReal) = ⊤ := by
  -- Off the domain, `extendWithTopOutside` is exactly the constant `⊤`.
  simpa [domainQuadraticPotential] using
    (ERealFunction.extendWithTopOutside_apply_of_not_mem
      (h := fun y : D ↦ (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) hx)

/-- The function `f` from Proposition 20.40, defined as the supremum of the affine defects
`⟪x, T y⟫_ℝ - h(y)` over `y ∈ D`. -/
noncomputable def supremalPotential
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) : H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨⨆ y : D, affineDefect T x y, supremalPotential_mem_Ioi D T x⟩

-- Proof sketch: unfold `supremalPotential`; its coercion to `EReal` is the defining supremum.
/-- Coercing `supremalPotential D T x` to `EReal` recovers the displayed supremum over `D`. -/
@[simp] theorem supremalPotential_apply
    (D : Submodule ℝ H) (T : D →ₗ[ℝ] H) (x : H) :
    (supremalPotential D T x : EReal) = ⨆ y : D, affineDefect T x y := by
  -- The subtype-valued definition was built from this supremum.
  rfl

end Potentials

section LinearSingleValuedOperators

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

variable (D : Submodule ℝ H) (T : D →ₗ[ℝ] H)

/-- Helper for Proposition 20.40: real affine functions, viewed in `EReal`, belong to `Γ(ℝ)`. -/
private theorem real_affine_mem_gamma (c : ℝ) :
    (fun t : ℝ ↦ ((t - c : ℝ) : EReal)) ∈ gamma ℝ := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · -- The one-dimensional affine formula satisfies Jensen's inequality by direct expansion.
    intro x y a ha0 ha1
    change (((a * x + (1 - a) * y - c : ℝ) : ℝ) : EReal) ≤
      (a : EReal) * ((x - c : ℝ) : EReal) + (1 - a : EReal) * ((y - c : ℝ) : EReal)
    exact le_of_eq <| by
      have hreal : a * x + (1 - a) * y - c = a * (x - c) + (1 - a) * (y - c) := by
        ring
      exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
  · -- Continuity of the affine representative upgrades to lower semicontinuity.
    simpa [Function.comp] using
      (continuous_coe_real_ereal.comp (continuous_id.sub continuous_const)).lowerSemicontinuous

omit [CompleteSpace H] in
/-- Helper for Proposition 20.40: for fixed `y ∈ D`, the affine branch
`x ↦ affineDefect T x y` belongs to `Γ(H)`. -/
private theorem affineDefect_mem_gamma_in_x (y : D) :
    (fun x : H ↦ affineDefect T x y) ∈ gamma H := by
  -- Compose the one-dimensional affine model with the continuous linear functional
  -- `x ↦ ⟪x, T y⟫`.
  have hcomp :=
    mem_gamma_comp_continuousLinearMap
      (fun t : ℝ ↦ ((t - ((1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ) : ℝ) : EReal))
      (innerSL ℝ (T y))
      (real_affine_mem_gamma ((1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ))
  simpa [Function.comp, affineDefect, innerSL_apply_apply, real_inner_comm] using hcomp

omit [CompleteSpace H] in
/-- Helper for Proposition 20.40: monotonicity and symmetry bound each affine branch by the
quadratic value at the base point. -/
private lemma affineDefect_le_quadratic_on_submodule
    (hT_symm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_mono : (ofFunction (D : Set H) T).IsMonotone)
    (x y : D) :
    affineDefect T (x : H) y ≤ (((1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ) : EReal) := by
  -- Expand the source monotonicity inequality at the graph points `(x, T x)` and `(y, T y)`.
  have hmono_xy : 0 ≤ ⟪(x : H) - y, T x - T y⟫_ℝ :=
    (SetValuedOperator.ofFunction_isMonotone_iff).1 hT_mono x y
  have hsymm_xy : ⟪(x : H), T y⟫_ℝ = ⟪(y : H), T x⟫_ℝ := by
    calc
      ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ := hT_symm x y
      _ = ⟪(y : H), T x⟫_ℝ := by rw [real_inner_comm]
  have hexpand :
      ⟪(x : H) - y, T x - T y⟫_ℝ =
        ⟪(x : H), T x⟫_ℝ + ⟪(y : H), T y⟫_ℝ - 2 * ⟪(x : H), T y⟫_ℝ := by
    -- Route correction: expand the monotonicity pairing once, then use symmetry to collapse the
    -- two mixed terms to the single source term `⟪x, T y⟫`.
    calc
      ⟪(x : H) - y, T x - T y⟫_ℝ
          = (⟪(x : H), T x⟫_ℝ - ⟪(x : H), T y⟫_ℝ) -
              (⟪(y : H), T x⟫_ℝ - ⟪(y : H), T y⟫_ℝ) := by
              rw [inner_sub_left, inner_sub_right, inner_sub_right]
      _ = ⟪(x : H), T x⟫_ℝ - ⟪(x : H), T y⟫_ℝ - ⟪(x : H), T y⟫_ℝ
            + ⟪(y : H), T y⟫_ℝ := by
            rw [hsymm_xy]
            ring
      _ = ⟪(x : H), T x⟫_ℝ + ⟪(y : H), T y⟫_ℝ - 2 * ⟪(x : H), T y⟫_ℝ := by ring
  have hreal :
      ⟪(x : H), T y⟫_ℝ - (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ
        ≤ (1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ := by
    rw [hexpand] at hmono_xy
    linarith
  change
    (((⟪(x : H), T y⟫_ℝ - (1 / 2 : ℝ) * ⟪(y : H), T y⟫_ℝ : ℝ) : EReal) ≤
      (((1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ : ℝ) : EReal))
  exact_mod_cast hreal

-- Proof sketch: identify `A` with the graph of `T` on `D`; the maximal monotonicity hypothesis
-- supplies the source assumptions and in particular implies monotonicity. Then rewrite
-- monotonicity of `A` as the quadratic inequality for `T`, and compare the supremum defining `f`
-- with the value at `y = x` and with the monotonicity bound obtained from
-- `0 ≤ ⟪x - y, T x - T y⟫`.
omit [CompleteSpace H] in
/-- Proposition 20.40 (1): if `A = ofFunction D T` is maximally monotone and `T` is symmetric on
`D`, then
the supremal potential `f` satisfies `f + ι_D = h`. -/
theorem supremalPotential_add_indicator_eq_domainQuadraticPotential
    (hT_symm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T)) :
    supremalPotential D T + ι[D] = domainQuadraticPotential D T := by
  funext x
  apply Subtype.ext
  by_cases hx : x ∈ D
  · have hmono : (ofFunction (D : Set H) T).IsMonotone := hT_max.1
    have hupper :
        (supremalPotential D T x : EReal) ≤
          (((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ) : EReal) := by
      -- Compare every branch of the defining supremum with the quadratic value at `x`.
      rw [supremalPotential_apply]
      refine iSup_le ?_
      intro y
      simpa using
        affineDefect_le_quadratic_on_submodule (D := D) (T := T) hT_symm hmono ⟨x, hx⟩ y
    have hx_branch :
        affineDefect T x ⟨x, hx⟩ =
          (((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ) : EReal) := by
      -- The witness `y = x` realizes equality in the source supremum.
      have hreal :
          ⟪x, T ⟨x, hx⟩⟫_ℝ - (1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ =
            (1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ := by
        ring
      calc
        affineDefect T x ⟨x, hx⟩
            = (((⟪x, T ⟨x, hx⟩⟫_ℝ - (1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ : ℝ)) : EReal) := by
                simp [affineDefect]
        _ = (((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ : ℝ) : EReal) := by
              exact congrArg (fun r : ℝ ↦ (r : EReal)) hreal
    have hlower :
        (((1 / 2 : ℝ) * ⟪x, T ⟨x, hx⟩⟫_ℝ) : EReal) ≤
          (supremalPotential D T x : EReal) := by
      rw [supremalPotential_apply]
      rw [← hx_branch]
      exact le_iSup (fun y : D ↦ affineDefect T x y) ⟨x, hx⟩
    -- On `D`, the indicator vanishes, so the source upper and lower bounds identify `f + ι_D`
    -- with the quadratic potential `h`.
    rw [domainQuadraticPotential_apply_of_mem D T hx]
    simpa [pointwiseAdd_apply, indicator_apply, hx] using le_antisymm hupper hlower
  · have hsup_ne_bot : (supremalPotential D T x : EReal) ≠ ⊥ :=
      ne_of_gt (supremalPotential D T x).property
    -- Outside `D`, the indicator and the extension-by-`⊤` owner both force the value `⊤`.
    rw [domainQuadraticPotential_apply_of_not_mem D T hx]
    simpa [indicator_apply, hx] using EReal.add_top_of_ne_bot hsup_ne_bot

-- Proof sketch: each term in the defining supremum of `f` is a continuous affine `EReal`-valued
-- function of `x`, so Proposition 9.3 gives membership in `Γ(H)` for the supremum. Properness
-- comes from the value at `0 ∈ D`, which is `0`, and clause (1) identifies the indicator-corrected
-- function with `h`.
omit [CompleteSpace H] in
/-- Proposition 20.40 (2): if `A = ofFunction D T` is maximally monotone and `T` is symmetric on
`D`, then
the supremal potential belongs to `Γ₀(H)`. -/
theorem supremalPotential_mem_gammaZero_of_maximalMonotone
    (hT_symm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T)) :
    supremalPotential D T ∈ Γ₀(H) := by
  let F : H → EReal := fun x ↦ ⨆ y : D, affineDefect T x y
  have hF_gamma : F ∈ gamma H := by
    -- Proposition 9.3 packages the source supremum once every affine branch lies in `Γ(H)`.
    dsimp [F]
    exact
      iSup_mem_gamma
        (f := fun y : D ↦ fun x : H ↦ affineDefect T x y)
        (hf := fun y ↦ affineDefect_mem_gamma_in_x (D := D) (T := T) y)
  have hF_proper : IsProper F := by
    refine ⟨?_, ?_⟩
    · -- The `y = 0` branch keeps the raw supremum strictly above `⊥` at every point.
      intro x
      have hgt : (⊥ : EReal) < F x := by
        simpa only [F] using supremalPotential_mem_Ioi D T x
      exact ne_of_gt hgt
    · -- Clause `(i)` evaluated at `0 ∈ D` gives the finite value `F 0 = 0`.
      refine ⟨0, (mem_dom_iff_ne_top F 0).2 ?_⟩
      have hzero_eq :
          (F 0 : EReal) = 0 := by
        have hpoint :=
          congrFun
            (supremalPotential_add_indicator_eq_domainQuadraticPotential
              (D := D) (T := T) hT_symm hT_max)
            0
        have hpointE :
            (((supremalPotential D T + ι[(D : Set H)]) 0 : Set.Ioi (⊥ : EReal)) : EReal) =
              (domainQuadraticPotential D T 0 : EReal) := by
          exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) hpoint
        simpa [F, pointwiseAdd_apply, indicator_apply,
          domainQuadraticPotential_apply_of_mem, D.zero_mem] using hpointE
      simp [hzero_eq]
  have hrepr : supremalPotential D T = properIoi F hF_proper := by
    -- Both packaged functions have the same `EReal` value pointwise; only the witness differs.
    funext x
    apply Subtype.ext
    simp [supremalPotential, F]
  rw [hrepr]
  -- Repackage the raw proper `Γ(H)` owner as a `Γ₀(H)` function.
  exact properIoi_mem_gammaZero_of_mem_gamma hF_proper hF_gamma

omit [CompleteSpace H] in
/-- Helper for Proposition 20.40: every graph point `(x, T x)` with `x ∈ D` is a subgradient of
the supremal potential at `x`. -/
private lemma mem_subdifferential_supremalPotential_of_mem_submodule
    (hT_symm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T))
    (x : D) :
    T x ∈ (∂ (supremalPotential D T)) (x : H) := by
  rw [mem_subdifferential_iff]
  intro y
  have hx_value :
      (supremalPotential D T (x : H) : EReal) =
        (((1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ) : EReal) := by
    have hpoint :=
      congrFun
        (supremalPotential_add_indicator_eq_domainQuadraticPotential
          (D := D) (T := T) hT_symm hT_max)
        (x : H)
    have hpointE :
        (((supremalPotential D T + ι[(D : Set H)]) (x : H) : Set.Ioi (⊥ : EReal)) : EReal) =
          (domainQuadraticPotential D T (x : H) : EReal) := by
      exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) hpoint
    simpa [pointwiseAdd_apply, indicator_apply, x.2,
      domainQuadraticPotential_apply_of_mem] using hpointE
  have hbranch_eq :
      ((⟪y - (x : H), T x⟫_ℝ : EReal) +
          (((1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ) : EReal)) =
        affineDefect T y x := by
    -- Route correction: rewrite the subgradient affine minorant to the exact branch appearing in
    -- the source supremum, rather than unfolding the whole supremum first.
    calc
      ((⟪y - (x : H), T x⟫_ℝ : EReal) +
          (((1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ) : EReal))
          = (((⟪y - (x : H), T x⟫_ℝ +
              (1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ : ℝ)) : EReal) := by
              rw [← EReal.coe_mul, ← EReal.coe_add]
      _ = (((⟪y, T x⟫_ℝ -
              (1 / 2 : ℝ) * ⟪(x : H), T x⟫_ℝ : ℝ)) : EReal) := by
            exact congrArg (fun r : ℝ ↦ (r : EReal)) <| by
              rw [inner_sub_left]
              ring
      _ = affineDefect T y x := by
            simp [affineDefect]
  calc
    (⟪y - (x : H), T x⟫_ℝ : EReal) + (supremalPotential D T (x : H) : EReal)
        = affineDefect T y x := by
            rw [hx_value, hbranch_eq]
    _ ≤ (supremalPotential D T y : EReal) := by
          rw [supremalPotential_apply]
          exact le_iSup (fun z : D ↦ affineDefect T y z) x

omit [CompleteSpace H] in
/-- Helper for Proposition 20.40: the domain of the singleton-valued operator attached to `T`
is exactly the submodule `D`. -/
private theorem dom_ofFunction_eq_submodule :
    SetValuedOperator.dom (ofFunction (D : Set H) T) = D := by
  ext x
  constructor
  · intro hx
    rw [SetValuedOperator.mem_dom_iff] at hx
    rcases hx with ⟨u, hu⟩
    rcases hu with ⟨hxD, _⟩
    exact hxD
  · intro hx
    rw [SetValuedOperator.mem_dom_iff]
    refine ⟨T ⟨x, hx⟩, ?_⟩
    exact ⟨hx, rfl⟩

-- Proof sketch: for `x ∈ D`, clause (1) gives `f x = h x`, so the affine minorant inequality with
-- slope `T x` is exactly the defining supremum bound; hence `T x ∈ ∂ f(x)` and the graph of
-- `A = ofFunction D T` is contained in `gra ∂f`. Maximal monotonicity of `A`, together with the
-- monotonicity of `∂f` from Example 20.3, forces equality of the two operators.
omit [CompleteSpace H] in
/-- Proposition 20.40 (3): if `A = ofFunction D T` is maximally monotone and `T` is symmetric on
`D`, then the subdifferential of the supremal potential is exactly `A`. -/
theorem subdifferential_supremalPotential_eq
    (hT_symm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T)) :
    ∂ (supremalPotential D T) = ofFunction (D : Set H) T := by
  have hGamma0 : supremalPotential D T ∈ Γ₀(H) :=
    supremalPotential_mem_gammaZero_of_maximalMonotone
      (D := D) (T := T) hT_symm hT_max
  have hsub : ofFunction (D : Set H) T ≤ ∂ (supremalPotential D T) := by
    -- Every graph point of `ofFunction D T` is one of the subgradients established above.
    intro x u hu
    rcases hu with ⟨hx, rfl⟩
    exact mem_subdifferential_supremalPotential_of_mem_submodule
      (D := D) (T := T) hT_symm hT_max ⟨x, hx⟩
  have hmono_sub : (∂ (supremalPotential D T)).IsMonotone := by
    -- Example 20.3 applies because clause `(ii)` already puts the supremal potential in `Γ₀(H)`.
    exact
      ERealFunction.subdifferential_isMonotone
        (f := supremalPotential D T)
        hGamma0.2.nonempty
  -- Maximality upgrades the graph inclusion to equality of operators.
  exact le_antisymm (hT_max.2 hmono_sub hsub) hsub

-- Proof sketch: clause (2) puts `f` in `Γ₀(H)`, so Corollary 16.41 identifies `f` with the
-- biconjugate of `f` plus the indicator of its subdifferentiability domain. Clause (3) rewrites
-- that domain as `D`, and clause (1) identifies the resulting function with `h`.
/-- Proposition 20.40 (4): if `A = ofFunction D T` is maximally monotone and `T` is symmetric on
`D`, then the supremal potential is the Fenchel biconjugate of `h`. -/
theorem supremalPotential_eq_biconjugate_domainQuadraticPotential
    (hT_symm : ∀ x y : D, ⟪(x : H), T y⟫_ℝ = ⟪T x, (y : H)⟫_ℝ)
    (hT_max : Maximal IsMonotone (ofFunction (D : Set H) T)) :
    (supremalPotential D T).asEReal = (domainQuadraticPotential D T).asEReal∗∗ := by
  have hGamma0 : supremalPotential D T ∈ Γ₀(H) :=
    supremalPotential_mem_gammaZero_of_maximalMonotone
      (D := D) (T := T) hT_symm hT_max
  have hsub_eq :
      ∂ (supremalPotential D T) = ofFunction (D : Set H) T :=
    subdifferential_supremalPotential_eq (D := D) (T := T) hT_symm hT_max
  have hdom_eq :
      SetValuedOperator.dom (∂ (supremalPotential D T)) = D := by
    rw [hsub_eq]
    exact dom_ofFunction_eq_submodule (D := D) (T := T)
  have hadd_eq :
      ((supremalPotential D T + ι[D]).asEReal) = (domainQuadraticPotential D T).asEReal := by
    -- Clause `(i)` already identifies the indicator-corrected function with `h`.
    funext x
    exact congrArg (fun z : Set.Ioi (⊥ : EReal) ↦ (z : EReal)) <|
      congrFun
        (supremalPotential_add_indicator_eq_domainQuadraticPotential
          (D := D) (T := T) hT_symm hT_max)
        x
  calc
    (supremalPotential D T).asEReal
        =
          ((supremalPotential D T +
              ι[SetValuedOperator.dom (∂ (supremalPotential D T))]).asEReal)∗∗ := by
            exact
              ERealFunction.eq_biconjugate_add_indicator_subdifferentiabilityDomain_of_mem_gammaZero
                hGamma0
    _ = ((supremalPotential D T + ι[D]).asEReal)∗∗ := by
          rw [hdom_eq]
    _ = (domainQuadraticPotential D T).asEReal∗∗ := by
          exact congrArg (fun g : H → EReal ↦ g∗∗) hadd_eq

end LinearSingleValuedOperators

end

end SetValuedOperator
