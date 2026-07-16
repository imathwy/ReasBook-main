import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_04.Example_1_23_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Example_8_17_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold
open NormedSpace

noncomputable section

local notation "SmoothVectorField" =>
  Cₛ^∞⟮𝓘(ℝ); ℝ, fun q : ℝ ↦ TangentSpace 𝓘(ℝ) q⟯

-- Domain sampling pass:
-- * primary domain: smooth vector fields on manifolds under `F`-relatedness along smooth maps;
-- * source-facing layer here: the cubic counterexample on `ℝ`;
-- * core/canonical owners sampled before refinement:
--   `cubicMap` for the cubic self-map of `ℝ`,
--   `Cₛ^∞⟮𝓘(ℝ); ℝ, TangentSpace 𝓘(ℝ)⟯` for smooth vector fields,
--   `VectorField.f_related`, `example_8_17_d_dt`,
--   and `NormedSpace.fromTangentSpace` for the tangent-space model of `d / dt`.
-- Primitive data here is reused entirely from the project owners `cubicMap` and
-- `example_8_17_d_dt`; smoothness and bijectivity facts for the map remain upstream derived API
-- rather than being recopied locally.

/- Any vector field on `ℝ` related to the chapter owner `example_8_17_d_dt` by the cubic map has
coordinate value `3x^2` at `x^3` under the canonical identification `T_{x^3}ℝ ≃ ℝ`. -/
theorem problem_8_9_related_value
    {Y : ∀ q : ℝ, TangentSpace 𝓘(ℝ) q}
    (hY : VectorField.f_related cubicMap example_8_17_d_dt Y)
    (x : ℝ) :
    fromTangentSpace (cubicMap x) (Y (cubicMap x)) = 3 * x ^ (2 : ℕ) := by
  -- Relatedness reduces to the scalar derivative of `x ↦ x^3` after applying
  -- `fromTangentSpace` on the codomain side.
  have hpush :
      (fderiv ℝ cubicMap x : ℝ → ℝ) 1 =
        fromTangentSpace (cubicMap x) (Y (cubicMap x)) := by
    simpa [cubicMap, example_8_17_d_dt] using
      congrArg (NormedSpace.fromTangentSpace (cubicMap x)) (VectorField.f_related_apply hY x)
  calc
    fromTangentSpace (cubicMap x) (Y (cubicMap x))
        = (fderiv ℝ cubicMap x : ℝ → ℝ) 1 := hpush.symm
    _ = deriv cubicMap x := by
      exact fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := cubicMap) (x := x)
    _ = 3 * x ^ (2 : ℕ) := by
      change deriv (fun y : ℝ ↦ y ^ (3 : ℕ)) x = 3 * x ^ (2 : ℕ)
      exact deriv_pow_field (𝕜 := ℝ) (x := x) 3

/-- Problem 8-9: the smooth bijection `x ↦ x^3` and the smooth vector field `d/dt` on `ℝ`
give a counterexample to the smooth-bijective analogue of Proposition 8.19, because there is no
bundled smooth vector field on `ℝ` that is `cubicMap`-related to
`example_8_17_d_dt`. -/
theorem problem_8_9_no_smooth_related_vector_field :
    ¬ ∃ Y : SmoothVectorField,
        VectorField.f_related
          cubicMap
          example_8_17_d_dt
          Y := by
  rintro ⟨Y, hrel⟩
  let g : ℝ → ℝ := fun q ↦ fromTangentSpace q (Y q)
  have hcomp : ∀ x : ℝ, g (cubicMap x) = 3 * x ^ (2 : ℕ) := by
    intro x
    -- The relatedness hypothesis already determines the coordinate value of `Y` at `x^3`.
    simpa [g] using problem_8_9_related_value hrel x
  have hYcoordMDiffAt :
      ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ g 0 := by
    have hY0 :
        ContMDiffAt 𝓘(ℝ) 𝓘(ℝ).tangent ∞
          (T% (Y : ∀ q : ℝ, TangentSpace 𝓘(ℝ) q)) 0 :=
      Y.contMDiff.contMDiffAt
    have hYcoordRaw :
        ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun q : ℝ ↦ Y q) 0 := by
    -- Smoothness of a tangent-bundle section is equivalent to smoothness of its trivialized
    -- coordinate function, and on the model space `ℝ` the trivialization is the identity.
      rw [Bundle.contMDiffAt_section 0] at hY0
      simpa [trivializationAt_model_space_apply] using hY0
    simpa [g] using hYcoordRaw
  have hg :
      ContDiffAt ℝ 2 g 0 := by
    have htwo_le_inf : (2 : ℕ∞ω) ≤ ∞ := by
      decide
    exact hYcoordMDiffAt.contDiffAt.of_le htwo_le_inf
  have hcubicInf :
      ContDiffAt ℝ ∞ cubicMap 0 := by
    simpa [cubicMap] using
      (((contDiff_id : ContDiff ℝ ∞ fun x : ℝ ↦ x).pow 3).contDiffAt :
        ContDiffAt ℝ ∞ (fun x : ℝ ↦ x ^ (3 : ℕ)) 0)
  have hcubic :
      ContDiffAt ℝ 2 cubicMap 0 := by
    have htwo_le_inf : (2 : ℕ∞ω) ≤ ∞ := by
      decide
    exact hcubicInf.of_le htwo_le_inf
  have hzero : iteratedDeriv 2 (g ∘ cubicMap) 0 = 0 := by
    have hgAtCube : ContDiffAt ℝ 2 g (cubicMap 0) := by
      simpa [cubicMap] using hg
    rw [iteratedDeriv_comp_two hgAtCube hcubic]
    have hderiv : deriv cubicMap 0 = 0 := by
      change deriv (fun y : ℝ ↦ y ^ (3 : ℕ)) 0 = 0
      norm_num [deriv_pow_field]
    have hsecond : iteratedDeriv 2 cubicMap 0 = 0 := by
      change iteratedDeriv 2 (fun y : ℝ ↦ y ^ (3 : ℕ)) 0 = 0
      norm_num [iteratedDeriv_pow]
    simp [hderiv, hsecond]
  have hquad : iteratedDeriv 2 (g ∘ cubicMap) 0 = 6 := by
    have hcompFun : g ∘ cubicMap = fun x : ℝ ↦ 3 * x ^ (2 : ℕ) := by
      ext x
      exact hcomp x
    rw [hcompFun]
    -- The forced coordinate formula is quadratic, so its second derivative at `0` is `6`.
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    simp [deriv_const_mul_field]
    norm_num
  norm_num [hquad] at hzero
