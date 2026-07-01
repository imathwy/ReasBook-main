/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib

section Chap06
section Section02

/-- Definition 6.7 (Derivative in one variable): let `E ⊆ ℝ`, `f : E → ℝ`, and
`x₀ ∈ E`. A real number `L` is the derivative of `f` at `x₀` iff
`(f x - f x₀) / (x - x₀)` tends to `L` as `x → x₀` with `x ∈ E \ {x₀}`. -/
def HasDerivativeInOneVariableAt
    (E : Set ℝ) (f : E → ℝ) (x₀ : E) (L : ℝ) : Prop :=
  Filter.Tendsto
    (fun x : E => (f x - f x₀) / ((x : ℝ) - (x₀ : ℝ)))
    (nhdsWithin x₀ {x : E | (x : ℝ) ≠ (x₀ : ℝ)})
    (nhds L)

/-- Helper for Lemma 6.4: pointwise algebraic identity relating the
linearization error ratio and the absolute difference quotient error. -/
lemma helperForLemma_6_4_pointwise_absErrorRatio_eq_absQuotientSub
    (E : Set ℝ) (f : E → ℝ) (x₀ : E) (L : ℝ)
    (x : E) (hx : (x : ℝ) ≠ (x₀ : ℝ)) :
    |f x - (f x₀ + L * ((x : ℝ) - (x₀ : ℝ)))| /
        |(x : ℝ) - (x₀ : ℝ)| =
      |((f x - f x₀) / ((x : ℝ) - (x₀ : ℝ))) - L| := by
  set d : ℝ := (x : ℝ) - (x₀ : ℝ)
  have hd : d ≠ 0 := by
    exact sub_ne_zero.mpr hx
  calc
    |f x - (f x₀ + L * ((x : ℝ) - (x₀ : ℝ)))| / |(x : ℝ) - (x₀ : ℝ)|
        = |(f x - (f x₀ + L * ((x : ℝ) - (x₀ : ℝ)))) /
            ((x : ℝ) - (x₀ : ℝ))| := by
          rw [← abs_div]
    _ = |((f x - f x₀) / ((x : ℝ) - (x₀ : ℝ))) - L| := by
          congr 1
          field_simp [hd, d]
          ring

/-- Helper for Lemma 6.4: on the punctured `nhdsWithin` filter, points are
eventually different from the basepoint. -/
lemma helperForLemma_6_4_eventually_ne_basepoint_on_puncturedFilter
    (E : Set ℝ) (x₀ : E) :
    ∀ᶠ x : E in nhdsWithin (X := E) x₀ {x : E | (x : ℝ) ≠ (x₀ : ℝ)},
      (x : ℝ) ≠ (x₀ : ℝ) := by
  exact self_mem_nhdsWithin

/-- Helper for Lemma 6.4: eventual equality between the target error ratio and
the absolute form `|quotient - L|` on the punctured filter. -/
lemma helperForLemma_6_4_eventuallyEq_errorRatio_absSubForm
    (E : Set ℝ) (f : E → ℝ) (x₀ : E) (L : ℝ) :
    (fun x : E =>
      |f x - (f x₀ + L * ((x : ℝ) - (x₀ : ℝ)))| /
        |(x : ℝ) - (x₀ : ℝ)|)
      =ᶠ[nhdsWithin x₀ {x : E | (x : ℝ) ≠ (x₀ : ℝ)}]
    (fun x : E => |((f x - f x₀) / ((x : ℝ) - (x₀ : ℝ))) - L|) := by
  filter_upwards [helperForLemma_6_4_eventually_ne_basepoint_on_puncturedFilter E x₀] with x hx
  simpa using helperForLemma_6_4_pointwise_absErrorRatio_eq_absQuotientSub E f x₀ L x hx

/-- Lemma 6.4: let `E ⊆ ℝ`, `f : E → ℝ`, `x₀ ∈ E` a limit point of `E`, and
`L ∈ ℝ`. Then `(f x - f x₀) / (x - x₀) → L` as `x → x₀` in `E \ {x₀}` iff
`|f x - (f x₀ + L (x - x₀))| / |x - x₀| → 0` on the same punctured domain. -/
lemma hasDerivativeInOneVariableAt_iff_tendsto_normErrorRatio_zero
    (E : Set ℝ) (f : E → ℝ) (x₀ : E) (L : ℝ)
    (hlimit : (x₀ : ℝ) ∈ closure (E \ {(x₀ : ℝ)})) :
    HasDerivativeInOneVariableAt E f x₀ L ↔
      Filter.Tendsto
        (fun x : E =>
          |f x - (f x₀ + L * ((x : ℝ) - (x₀ : ℝ)))| /
            |(x : ℝ) - (x₀ : ℝ)|)
        (nhdsWithin x₀ {x : E | (x : ℝ) ≠ (x₀ : ℝ)})
        (nhds (0 : ℝ)) := by
  let punctured : Set E := {x : E | (x : ℝ) ≠ (x₀ : ℝ)}
  let quotient : E → ℝ := fun x => (f x - f x₀) / ((x : ℝ) - (x₀ : ℝ))
  let errorRatio : E → ℝ :=
    fun x =>
      |f x - (f x₀ + L * ((x : ℝ) - (x₀ : ℝ)))| /
        |(x : ℝ) - (x₀ : ℝ)|
  have hEventualEq :
      errorRatio =ᶠ[nhdsWithin x₀ punctured]
        (fun x : E => |quotient x - L|) := by
    simpa [punctured, quotient, errorRatio] using
      helperForLemma_6_4_eventuallyEq_errorRatio_absSubForm E f x₀ L
  constructor
  · intro hDeriv
    have hQuotient :
        Filter.Tendsto quotient (nhdsWithin x₀ punctured) (nhds L) := by
      simpa [HasDerivativeInOneVariableAt, punctured, quotient] using hDeriv
    have hNormSub :
        Filter.Tendsto (fun x : E => ‖quotient x - L‖)
          (nhdsWithin x₀ punctured) (nhds (0 : ℝ)) := by
      exact (tendsto_iff_norm_sub_tendsto_zero).1 hQuotient
    have hAbsSub :
        Filter.Tendsto (fun x : E => |quotient x - L|)
          (nhdsWithin x₀ punctured) (nhds (0 : ℝ)) := by
      simpa [Real.norm_eq_abs] using hNormSub
    have hErrorRatio :
        Filter.Tendsto errorRatio (nhdsWithin x₀ punctured) (nhds (0 : ℝ)) := by
      exact Filter.Tendsto.congr' hEventualEq.symm hAbsSub
    simpa [punctured, errorRatio] using hErrorRatio
  · intro hError
    have hErrorRatio :
        Filter.Tendsto errorRatio (nhdsWithin x₀ punctured) (nhds (0 : ℝ)) := by
      simpa [punctured, errorRatio] using hError
    have hAbsSub :
        Filter.Tendsto (fun x : E => |quotient x - L|)
          (nhdsWithin x₀ punctured) (nhds (0 : ℝ)) := by
      exact Filter.Tendsto.congr' hEventualEq hErrorRatio
    have hNormSub :
        Filter.Tendsto (fun x : E => ‖quotient x - L‖)
          (nhdsWithin x₀ punctured) (nhds (0 : ℝ)) := by
      simpa [Real.norm_eq_abs] using hAbsSub
    have hQuotient :
        Filter.Tendsto quotient (nhdsWithin x₀ punctured) (nhds L) := by
      exact (tendsto_iff_norm_sub_tendsto_zero).2 hNormSub
    simpa [HasDerivativeInOneVariableAt, punctured, quotient] using hQuotient

/-- Definition 6.8 (Differentiability): let `E ⊆ ℝ^n`, `f : E → ℝ^m`, and
`x₀ ∈ E` be a limit point of `E`. For a linear map `L : ℝ^n → ℝ^m`, `f` is
differentiable at `x₀` with derivative `L` when
`‖f x - (f x₀ + L (x - x₀))‖ / ‖x - x₀‖ → 0` as `x → x₀` with
`x ∈ E \ {x₀}`, using the Euclidean norm. -/
def HasDerivativeInSeveralVariablesAt
    (n m : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : E → EuclideanSpace ℝ (Fin m))
    (x₀ : E)
    (L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : Prop :=
  ((x₀ : EuclideanSpace ℝ (Fin n)) ∈ closure (E \ {(x₀ : EuclideanSpace ℝ (Fin n))})) ∧
    Filter.Tendsto
      (fun x : E =>
        ‖f x - (f x₀ + L ((x : EuclideanSpace ℝ (Fin n)) - (x₀ : EuclideanSpace ℝ (Fin n))))‖ /
          ‖(x : EuclideanSpace ℝ (Fin n)) - (x₀ : EuclideanSpace ℝ (Fin n))‖)
      (nhdsWithin x₀ {x : E | x ≠ x₀})
      (nhds (0 : ℝ))

/-- Helper for Proposition 6.8: the basepoint lies in the closure of the punctured universe. -/
lemma helperForProposition_6_8_memClosure_univ_diff_singleton
    (x₀ : EuclideanSpace ℝ (Fin 2)) :
    x₀ ∈ closure ((Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {x₀}) := by
  have hdense : Dense ({x₀}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := dense_compl_singleton x₀
  have hclosure : closure ({x₀}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) = Set.univ := hdense.closure_eq
  have hmem : x₀ ∈ closure ({x₀}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    simpa [hclosure]
  have hset :
      ((Set.univ : Set (EuclideanSpace ℝ (Fin 2))) \ {x₀}) =
        ({x₀}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    simp
  simpa [hset] using hmem

/-- Helper for Proposition 6.8: the map `f` agrees with the coordinate-square formula. -/
lemma helperForProposition_6_8_f_eq_coordinateSquare_onSubtypeUniv
    (f : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} →
      EuclideanSpace ℝ (Fin 2))
    (hf₀ : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))},
      (f p) 0 = ((p : EuclideanSpace ℝ (Fin 2)) 0) ^ (2 : ℕ))
    (hf₁ : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))},
      (f p) 1 = ((p : EuclideanSpace ℝ (Fin 2)) 1) ^ (2 : ℕ))
    (p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))}) :
    f p = (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (fun i : Fin 2 => ((p : EuclideanSpace ℝ (Fin 2)) i) ^ (2 : ℕ)) := by
  ext i
  fin_cases i
  · simp [hf₀]
  · simp [hf₁]

/-- Helper for Proposition 6.8: the coordinate-square ambient map has derivative `L` at `x₀`. -/
lemma helperForProposition_6_8_hasFDerivAt_coordinateSquare_at_x0
    (x₀ : EuclideanSpace ℝ (Fin 2))
    (hx₀₀ : x₀ 0 = (1 : ℝ))
    (hx₀₁ : x₀ 1 = (2 : ℝ))
    (L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hL₀ : ∀ v : EuclideanSpace ℝ (Fin 2), (L v) 0 = (2 : ℝ) * v 0)
    (hL₁ : ∀ v : EuclideanSpace ℝ (Fin 2), (L v) 1 = (4 : ℝ) * v 1) :
    HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)))
      (LinearMap.toContinuousLinearMap L)
      x₀ := by
  let φ' : Fin 2 → EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    fun i => ((2 : ℝ) * x₀ i) • (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i)
  have hφ :
      HasFDerivAt
        (fun x : EuclideanSpace ℝ (Fin 2) => (fun i : Fin 2 => (x i) ^ (2 : ℕ)))
        (ContinuousLinearMap.pi φ')
        x₀ := by
    refine (hasFDerivAt_pi).2 ?_
    intro i
    simpa [φ', pow_one, one_mul, smul_smul, mul_assoc] using
      ((EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).hasFDerivAt.pow (2 : ℕ) (x := x₀))
  have hsymm : HasFDerivAt
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap
      ((fun i : Fin 2 => (x₀ i) ^ (2 : ℕ))) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.hasFDerivAt
  have hDerivM : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)))
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi φ'))
      x₀ := by
    simpa [Function.comp] using hsymm.comp x₀ hφ
  have hCoeff0 : (2 : ℝ) * x₀ 0 = 2 := by nlinarith [hx₀₀]
  have hCoeff1 : (2 : ℝ) * x₀ 1 = 4 := by nlinarith [hx₀₁]
  have hLext :
      (LinearMap.toContinuousLinearMap L) =
        ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearMap.comp (ContinuousLinearMap.pi φ')) := by
    ext v i
    fin_cases i
    · simp [φ', hL₀, hCoeff0]
    · simp [φ', hL₁, hCoeff1]
  simpa [hLext] using hDerivM

/-- Helper for Proposition 6.8: the linearization error ratio tends to `0` on punctured neighborhoods in the ambient space. -/
lemma helperForProposition_6_8_tendsto_errorRatio_on_puncturedAmbient
    (x₀ : EuclideanSpace ℝ (Fin 2))
    (L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hFDeriv : HasFDerivAt
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)))
      (LinearMap.toContinuousLinearMap L)
      x₀) :
    Filter.Tendsto
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)) -
            ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x₀ i) ^ (2 : ℕ)) +
              L (x - x₀))‖ /
          ‖x - x₀‖)
      (nhdsWithin x₀ {x : EuclideanSpace ℝ (Fin 2) | x ≠ x₀})
      (nhds (0 : ℝ)) := by
  have hLittle :
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)) -
          ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x₀ i) ^ (2 : ℕ)) +
            L (x - x₀)))
        =o[nhds x₀]
      (fun x : EuclideanSpace ℝ (Fin 2) => x - x₀) := by
    simpa [LinearMap.map_sub, sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hFDeriv.isLittleO
  have hLittleWithin :
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)) -
          ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x₀ i) ^ (2 : ℕ)) +
            L (x - x₀)))
        =o[nhdsWithin x₀ {x : EuclideanSpace ℝ (Fin 2) | x ≠ x₀}]
      (fun x : EuclideanSpace ℝ (Fin 2) => x - x₀) :=
    hLittle.mono nhdsWithin_le_nhds
  have hNormLittle :
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)) -
            ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x₀ i) ^ (2 : ℕ)) +
              L (x - x₀))‖)
        =o[nhdsWithin x₀ {x : EuclideanSpace ℝ (Fin 2) | x ≠ x₀}]
      (fun x : EuclideanSpace ℝ (Fin 2) => x - x₀) :=
    hLittleWithin.norm_left
  have hNormNormLittle :
      (fun x : EuclideanSpace ℝ (Fin 2) =>
        ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ)) -
            ((EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x₀ i) ^ (2 : ℕ)) +
              L (x - x₀))‖)
        =o[nhdsWithin x₀ {x : EuclideanSpace ℝ (Fin 2) | x ≠ x₀}]
      (fun x : EuclideanSpace ℝ (Fin 2) => ‖x - x₀‖) :=
    hNormLittle.norm_right
  simpa using hNormNormLittle.tendsto_div_nhds_zero

/-- Helper for Proposition 6.8: punctured neighborhood filters on `Subtype univ` agree with the ambient punctured filter via coercion. -/
lemma helperForProposition_6_8_nhdsWithin_puncturedSubtypeUniv_eq_comap
    (x₀ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))}) :
    nhdsWithin x₀ {x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} | x ≠ x₀} =
      Filter.comap (fun x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} =>
        (x : EuclideanSpace ℝ (Fin 2)))
        (nhdsWithin (x₀ : EuclideanSpace ℝ (Fin 2))
          {x : EuclideanSpace ℝ (Fin 2) | x ≠ (x₀ : EuclideanSpace ℝ (Fin 2))}) := by
  have hImage :
      (Subtype.val ''
        ({x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} | x ≠ x₀})) =
      ({x : EuclideanSpace ℝ (Fin 2) | x ≠ (x₀ : EuclideanSpace ℝ (Fin 2))}) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      intro hEq
      exact hy (Subtype.ext hEq)
    · intro hx
      have hxUniv : x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2))) := by
        simp
      let xSub : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} :=
        ⟨x, hxUniv⟩
      have hx' : xSub ≠ x₀ := by
        intro hSub
        exact hx (congrArg Subtype.val hSub)
      exact ⟨xSub, hx', rfl⟩
  simpa [hImage] using
    (nhdsWithin_subtype
      (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))
      x₀
      ({x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} | x ≠ x₀}))

/-- Proposition 6.8: if `f : ℝ² → ℝ²` is given by `f(x, y) = (x^2, y^2)`, then
`f` is differentiable at `x₀ = (1, 2)` with derivative `L(x, y) = (2x, 4y)`. -/
theorem hasDerivativeInSeveralVariablesAt_coordinateSquare_at_one_two
    (x₀ : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))})
    (hx₀₀ : (x₀ : EuclideanSpace ℝ (Fin 2)) 0 = (1 : ℝ))
    (hx₀₁ : (x₀ : EuclideanSpace ℝ (Fin 2)) 1 = (2 : ℝ))
    (f : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} →
      EuclideanSpace ℝ (Fin 2))
    (hf₀ : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))},
      (f p) 0 = ((p : EuclideanSpace ℝ (Fin 2)) 0) ^ (2 : ℕ))
    (hf₁ : ∀ p : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))},
      (f p) 1 = ((p : EuclideanSpace ℝ (Fin 2)) 1) ^ (2 : ℕ))
    (L : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hL₀ : ∀ v : EuclideanSpace ℝ (Fin 2), (L v) 0 = (2 : ℝ) * v 0)
    (hL₁ : ∀ v : EuclideanSpace ℝ (Fin 2), (L v) 1 = (4 : ℝ) * v 1) :
    HasDerivativeInSeveralVariablesAt
      2 2
      (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))
      f
      x₀
      L := by
  refine And.intro ?_ ?_
  · exact helperForProposition_6_8_memClosure_univ_diff_singleton (x₀ := (x₀ : EuclideanSpace ℝ (Fin 2)))
  · let coordinateSquare : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
      fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm (fun i : Fin 2 => (x i) ^ (2 : ℕ))
    let coordinateSquareSubtype :
        {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} →
          EuclideanSpace ℝ (Fin 2) :=
      fun x => coordinateSquare (x : EuclideanSpace ℝ (Fin 2))
    have hFDeriv :
        HasFDerivAt coordinateSquare (LinearMap.toContinuousLinearMap L) (x₀ : EuclideanSpace ℝ (Fin 2)) :=
      helperForProposition_6_8_hasFDerivAt_coordinateSquare_at_x0
        (x₀ := (x₀ : EuclideanSpace ℝ (Fin 2))) hx₀₀ hx₀₁ L hL₀ hL₁
    have hAmbientTendsto :
        Filter.Tendsto
          (fun x : EuclideanSpace ℝ (Fin 2) =>
            ‖coordinateSquare x - (coordinateSquare (x₀ : EuclideanSpace ℝ (Fin 2)) + L (x - (x₀ : EuclideanSpace ℝ (Fin 2))))‖ /
              ‖x - (x₀ : EuclideanSpace ℝ (Fin 2))‖)
          (nhdsWithin (x₀ : EuclideanSpace ℝ (Fin 2))
            {x : EuclideanSpace ℝ (Fin 2) | x ≠ (x₀ : EuclideanSpace ℝ (Fin 2))})
          (nhds (0 : ℝ)) := by
      simpa [coordinateSquare] using
        helperForProposition_6_8_tendsto_errorRatio_on_puncturedAmbient
          (x₀ := (x₀ : EuclideanSpace ℝ (Fin 2)))
          (L := L)
          hFDeriv
    have hSubtypeTendsto :
        Filter.Tendsto
          (fun x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} =>
            ‖coordinateSquareSubtype x -
                (coordinateSquareSubtype x₀ + L ((x : EuclideanSpace ℝ (Fin 2)) - (x₀ : EuclideanSpace ℝ (Fin 2))))‖ /
              ‖(x : EuclideanSpace ℝ (Fin 2)) - (x₀ : EuclideanSpace ℝ (Fin 2))‖)
          (nhdsWithin x₀ {x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} | x ≠ x₀})
          (nhds (0 : ℝ)) := by
      rw [helperForProposition_6_8_nhdsWithin_puncturedSubtypeUniv_eq_comap (x₀ := x₀)]
      exact hAmbientTendsto.comp Filter.tendsto_comap
    have hfEqAtX :
        ∀ x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))},
          f x = coordinateSquareSubtype x := by
      intro x
      simpa [coordinateSquareSubtype, coordinateSquare] using
        helperForProposition_6_8_f_eq_coordinateSquare_onSubtypeUniv f hf₀ hf₁ x
    have hTargetEq :
        (fun x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} =>
          ‖f x - (f x₀ + L ((x : EuclideanSpace ℝ (Fin 2)) - (x₀ : EuclideanSpace ℝ (Fin 2))))‖ /
            ‖(x : EuclideanSpace ℝ (Fin 2)) - (x₀ : EuclideanSpace ℝ (Fin 2))‖)
          =
        (fun x : {x : EuclideanSpace ℝ (Fin 2) // x ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin 2)))} =>
          ‖coordinateSquareSubtype x -
              (coordinateSquareSubtype x₀ + L ((x : EuclideanSpace ℝ (Fin 2)) - (x₀ : EuclideanSpace ℝ (Fin 2))))‖ /
            ‖(x : EuclideanSpace ℝ (Fin 2)) - (x₀ : EuclideanSpace ℝ (Fin 2))‖) := by
      funext x
      simp [hfEqAtX x, hfEqAtX x₀]
    rw [hTargetEq]
    exact hSubtypeTendsto

/-- Lemma 6.5 (Uniqueness of derivatives): if `x₀` is an interior point of
`E ⊆ ℝⁿ` and both `L₁` and `L₂` satisfy the derivative error-ratio limit for
`f : E → ℝᵐ` at `x₀`, then the linear transformations coincide: `L₁ = L₂`. -/
theorem derivativeInSeveralVariables_unique
    (n m : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : E → EuclideanSpace ℝ (Fin m))
    (x₀ : E)
    (hinterior : (x₀ : EuclideanSpace ℝ (Fin n)) ∈ interior E)
    (L₁ L₂ : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))
    (hL₁ : HasDerivativeInSeveralVariablesAt n m E f x₀ L₁)
    (hL₂ : HasDerivativeInSeveralVariablesAt n m E f x₀ L₂) :
    L₁ = L₂ := by
  classical
  let fExt : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) :=
    fun x => if hx : x ∈ E then f ⟨x, hx⟩ else f x₀
  have hHasFDerivWithin_of_custom :
      ∀ L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m),
        HasDerivativeInSeveralVariablesAt n m E f x₀ L →
          HasFDerivWithinAt
            fExt
            (LinearMap.toContinuousLinearMap L)
            E
            (x₀ : EuclideanSpace ℝ (Fin n)) := by
    intro L hL
    let θ : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x =>
        ‖x - (x₀ : EuclideanSpace ℝ (Fin n))‖⁻¹ *
          ‖fExt x -
              fExt (x₀ : EuclideanSpace ℝ (Fin n)) -
              (LinearMap.toContinuousLinearMap L) (x - (x₀ : EuclideanSpace ℝ (Fin n)))‖
    let ψ : E → ℝ := E.restrict θ
    have hψ_eq_target :
        ψ =
          (fun x : E =>
            ‖f x -
                (f x₀ +
                  L ((x : EuclideanSpace ℝ (Fin n)) - (x₀ : EuclideanSpace ℝ (Fin n))))‖ /
              ‖(x : EuclideanSpace ℝ (Fin n)) - (x₀ : EuclideanSpace ℝ (Fin n))‖) := by
      funext x
      simp [ψ, θ, fExt, div_eq_inv_mul, sub_eq_add_neg, add_assoc, add_comm]
    have hPunct :
        Filter.Tendsto
          ψ
          (nhdsWithin x₀ {x : E | x ≠ x₀})
          (nhds (0 : ℝ)) := by
      rw [hψ_eq_target]
      exact hL.2
    have hψx₀ : ψ x₀ = 0 := by
      simp [ψ, θ, fExt]
    have hPure :
        Filter.Tendsto ψ (pure x₀) (nhds (0 : ℝ)) := by
      simpa [hψx₀] using (tendsto_pure_nhds ψ x₀)
    have hSetNe : ({x : E | x ≠ x₀} : Set E) = ({x₀}ᶜ : Set E) := by
      ext x
      simp
    have hPunctCompl :
        Filter.Tendsto
          ψ
          (nhdsWithin x₀ ({x₀}ᶜ : Set E))
          (nhds (0 : ℝ)) := by
      simpa [hSetNe] using hPunct
    have hSubtype :
        Filter.Tendsto
          ψ
          (nhds x₀)
          (nhds (0 : ℝ)) := by
      have hSup :
          Filter.Tendsto
            ψ
            (pure x₀ ⊔ nhdsWithin x₀ ({x₀}ᶜ : Set E))
            (nhds (0 : ℝ)) :=
        hPure.sup hPunctCompl
      simpa [pure_sup_nhdsNE] using hSup
    have hAmbient :
        Filter.Tendsto
          θ
          (nhdsWithin (x₀ : EuclideanSpace ℝ (Fin n)) E)
          (nhds (0 : ℝ)) :=
      (tendsto_nhdsWithin_iff_subtype
        (s := E)
        (h := x₀.property)
        θ
        (nhds (0 : ℝ))).2 hSubtype
    rw [hasFDerivWithinAt_iff_tendsto]
    simpa [θ] using hAmbient
  have hFDeriv₁ :
      HasFDerivWithinAt
        fExt
        (LinearMap.toContinuousLinearMap L₁)
        E
        (x₀ : EuclideanSpace ℝ (Fin n)) :=
    hHasFDerivWithin_of_custom L₁ hL₁
  have hFDeriv₂ :
      HasFDerivWithinAt
        fExt
        (LinearMap.toContinuousLinearMap L₂)
        E
        (x₀ : EuclideanSpace ℝ (Fin n)) :=
    hHasFDerivWithin_of_custom L₂ hL₂
  have hUniqueDiff :
      UniqueDiffWithinAt
        ℝ
        E
        (x₀ : EuclideanSpace ℝ (Fin n)) :=
    uniqueDiffWithinAt_of_mem_nhds (mem_interior_iff_mem_nhds.mp hinterior)
  have hEqCLM :
      LinearMap.toContinuousLinearMap L₁ =
        LinearMap.toContinuousLinearMap L₂ :=
    hUniqueDiff.eq hFDeriv₁ hFDeriv₂
  ext v i
  exact congrArg
    (fun T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m) => (T v) i)
    hEqCLM

end Section02
end Chap06
