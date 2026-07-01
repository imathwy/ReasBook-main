/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Yi Yuan, Zaiwen Wen
-/

import Mathlib
import Books.Analysis2_Tao_2022.Chapters.Chap06.section03_part1

section Chap06
section Section03

open scoped Topology

/-- Helper for Lemma 6.6: when the directional value `f' v` is zero, the theorem's
unpunctured directional-limit target follows from the established equivalence with
`f' v = 0`. -/
lemma helperForLemma_6_6_target_tendsto_of_zero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v = 0) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  exact
    (helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd).2 hv0

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, if
`f' v ≠ 0` then any proof of the theorem's unpunctured directional-limit target yields
`False`. -/
lemma helperForLemma_6_6_false_of_target_tendsto_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0)
    (htarget : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) :
    False := by
  exact hv0 ((helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd).1 htarget)

/-- Helper for Lemma 6.6: any implication that turns differentiability data into the theorem's
unpunctured directional-limit target forces the directional value `f' v` to be zero. -/
lemma helperForLemma_6_6_target_implication_forces_directionalValue_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (himp :
      HasFDerivWithinAt f f' E x₀ →
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) :
    HasFDerivWithinAt f f' E x₀ →
      f' v = 0 := by
  intro hfd
  exact helperForLemma_6_6_unpunctured_limit_forces_zero
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    (himp hfd)

/-- Helper for Lemma 6.6: with fixed differentiability data, a nonzero directional value
makes any implication to the theorem's unpunctured target claim contradictory. -/
lemma helperForLemma_6_6_false_of_target_implication_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0)
    (himp :
      HasFDerivWithinAt f f' E x₀ →
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) :
    False := by
  have hzero : f' v = 0 :=
    (helperForLemma_6_6_target_implication_forces_directionalValue_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      himp) hfd
  exact hv0 hzero

/-- Helper for Lemma 6.6: once differentiability data is fixed, a nonzero directional value
precludes any implication from that data to the theorem's unpunctured target claim. -/
lemma helperForLemma_6_6_no_target_implication_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    ¬ (HasFDerivWithinAt f f' E x₀ →
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) := by
  intro himp
  exact helperForLemma_6_6_false_of_target_implication_of_nonzero_directionalValue
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd
    hv0
    himp

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, if
`f' v ≠ 0` then the theorem's unpunctured directional-limit target is equivalent to
`False`. -/
lemma helperForLemma_6_6_target_tendsto_iff_false_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    (Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔ False := by
  constructor
  · intro htarget
    exact helperForLemma_6_6_false_of_target_tendsto_of_nonzero_directionalValue
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
      hv0
      htarget
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, the theorem's
unpunctured directional-limit target is equivalent to the conjunction of the punctured
directional limit and the vanishing directional value `f' v = 0`. -/
lemma helperForLemma_6_6_target_tendsto_iff_zero_and_punctured
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀) :
    (Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) ↔
      (f' v = 0 ∧
        Filter.Tendsto
          (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
          (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
          (𝓝 (f' v))) := by
  constructor
  · intro htarget
    refine ⟨?_, ?_⟩
    · exact (helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
        (x₀ := x₀)
        (v := v)
        (f' := f')
        hx₀
        hfd).1 htarget
    · exact helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
        (x₀ := x₀)
        (v := v)
        (hx₀ := hx₀)
        (hfd := hfd)
  · rintro ⟨hzero, hpunctured⟩
    exact helperForLemma_6_6_unpunctured_limit_of_punctured_limit_and_zero_directional_value
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hpunctured
      hzero

/-- Helper for Lemma 6.6: if the theorem's unpunctured target claim is equivalent to
`f' v = 0` together with the punctured directional-limit claim, then any nonzero
directional value `f' v` excludes the unpunctured target claim. -/
lemma helperForLemma_6_6_not_target_of_targetIff_zero_and_punctured_and_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (htargetIffZeroAndPunctured :
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
        (f' v = 0 ∧
          Filter.Tendsto
            (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
            (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
            (𝓝 (f' v))))
    (hv0 : f' v ≠ 0) :
    ¬ Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  intro htarget
  exact hv0 (htargetIffZeroAndPunctured.mp htarget).1

/-- Helper for Lemma 6.6: for fixed differentiability data at an interior point,
combining a nonzero directional value `f' v ≠ 0` with the theorem's unpunctured
target claim yields a contradiction. -/
lemma helperForLemma_6_6_false_of_nonzero_directionalValue_and_targetClaim
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0)
    (htarget : Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
      (𝓝 (f' v))) :
    False := by
  exact hv0
    ((helperForLemma_6_6_target_tendsto_iff_directionalValue_eq_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd).1 htarget)

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, if
`f' v ≠ 0` then the theorem's unpunctured directional-limit target proposition is empty. -/
lemma helperForLemma_6_6_target_tendsto_isEmpty_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    IsEmpty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) := by
  refine ⟨?_⟩
  intro htarget
  exact helperForLemma_6_6_false_of_nonzero_directionalValue_and_targetClaim
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd
    hv0
    htarget

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, if
`f' v ≠ 0` then the theorem's unpunctured directional-limit target proposition has no
inhabitants. -/
lemma helperForLemma_6_6_target_tendsto_not_nonempty_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    ¬ Nonempty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) := by
  intro hnonempty
  rcases hnonempty with ⟨htarget⟩
  exact (helperForLemma_6_6_target_tendsto_iff_false_of_nonzero_directionalValue
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd
    hv0).1 htarget

/-- Helper for Lemma 6.6: if the theorem's unpunctured directional-limit target proposition is
inhabited for fixed interior-point data, then the directional value `f' v` must be zero. -/
lemma helperForLemma_6_6_target_tendsto_nonempty_forces_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hnonempty : Nonempty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v)))) :
    f' v = 0 := by
  rcases hnonempty with ⟨htarget⟩
  exact helperForLemma_6_6_target_claim_forces_zero
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    htarget

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, inhabitation of
the theorem's unpunctured directional-limit target proposition is equivalent to `f' v = 0`. -/
lemma helperForLemma_6_6_target_tendsto_nonempty_iff_directionalValue_eq_zero
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀) :
    Nonempty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
      f' v = 0 := by
  constructor
  · intro hnonempty
    exact helperForLemma_6_6_target_tendsto_nonempty_forces_zero
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hnonempty
  · intro hv0
    refine ⟨?_⟩
    exact helperForLemma_6_6_target_tendsto_of_zero_directionalValue
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
      hv0

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, the theorem's
unpunctured directional-limit target proposition is empty exactly when the directional value
`f' v` is nonzero. -/
lemma helperForLemma_6_6_target_tendsto_isEmpty_iff_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀) :
    IsEmpty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
      f' v ≠ 0 := by
  constructor
  · intro hEmpty
    intro hzero
    have htarget :
        Filter.Tendsto
          (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
          (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
          (𝓝 (f' v)) :=
      helperForLemma_6_6_target_tendsto_of_zero_directionalValue
        (x₀ := x₀)
        (v := v)
        (f' := f')
        hx₀
        hfd
        hzero
    exact hEmpty.false htarget
  · intro hv0
    exact helperForLemma_6_6_target_tendsto_isEmpty_of_nonzero_directionalValue
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
      hv0

/-- Helper for Lemma 6.6: for fixed differentiable data at an interior point, if
`f' v ≠ 0` then inhabitation of the theorem's unpunctured directional-limit target proposition
is equivalent to `False`. -/
lemma helperForLemma_6_6_target_tendsto_nonempty_iff_false_of_nonzero_directionalValue
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    Nonempty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) ↔
      False := by
  constructor
  · intro hnonempty
    exact helperForLemma_6_6_target_tendsto_not_nonempty_of_nonzero_directionalValue
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
      hv0
      hnonempty
  · intro hFalse
    exact False.elim hFalse

/-- Helper for Lemma 6.6: in the nonzero directional-value branch, differentiability still
gives the punctured directional limit, while the theorem's unpunctured target proposition is
empty. -/
lemma helperForLemma_6_6_nonzero_branch_punctured_limit_and_empty_target
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (hv0 : f' v ≠ 0) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)) ∧
    IsEmpty
      (Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | x₀ + t • v ∈ E})
        (𝓝 (f' v))) := by
  refine ⟨?_, ?_⟩
  · exact helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
      (x₀ := x₀)
      (v := v)
      (hx₀ := hx₀)
      (hfd := hfd)
  · exact helperForLemma_6_6_target_tendsto_isEmpty_of_nonzero_directionalValue
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
      hv0

/-- Lemma 6.6: Let `E ⊆ ℝⁿ`, `f : E → ℝᵐ` (represented by an ambient map with
within-domain derivative), and `x₀ ∈ interior E`. If `f` is differentiable at `x₀`
within `E` with derivative `f'`, then the directional derivative at `x₀` in direction `v`
exists as `t → 0` along nonzero points with `x₀ + t v ∈ E`, and equals `f' v`. -/
theorem hasDirectionalDerivWithinAt_eq_fderiv
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {v : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (f' v)) := by
  exact helperForLemma_6_6_punctured_directional_limit_of_hasFDerivWithinAt
    (x₀ := x₀)
    (v := v)
    (f' := f')
    hx₀
    hfd

/-- The `j`-th standard basis vector in `ℝⁿ`, viewed as an element of `EuclideanSpace`. -/
noncomputable def standardBasisVectorEuclidean (n : ℕ) (j : Fin n) : EuclideanSpace ℝ (Fin n) :=
  EuclideanSpace.single j 1

/-- The difference quotient used to define the partial derivative of `f` with respect to the
`j`-th coordinate at `x₀`. -/
noncomputable def partialDifferenceQuotientWithin
    {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (j : Fin n) :
    ℝ → EuclideanSpace ℝ (Fin m) :=
  fun t =>
    t⁻¹ • (f (x₀ + t • standardBasisVectorEuclidean n j) - f x₀)

/-- The within-`E` partial derivative notion (equation 6.u77): for `E ⊆ ℝⁿ`, ambient extension
`f : ℝⁿ → ℝᵐ` of the book map `E → ℝᵐ`, interior `x₀ ∈ E`, and coordinate `j`,
`HasPartialDerivWithinAt E f x₀ j L` records that the constrained difference quotient along `e_j`
converges to `L` as `t → 0` through nonzero values with `x₀ + t e_j ∈ E`. -/
def HasPartialDerivWithinAt
    {n m : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (j : Fin n)
    (L : EuclideanSpace ℝ (Fin m)) : Prop :=
  x₀ ∈ interior E ∧
    Filter.Tendsto
      (partialDifferenceQuotientWithin f x₀ j)
      (nhdsWithin (0 : ℝ)
        {t : ℝ |
          t ≠ 0 ∧ x₀ + t • standardBasisVectorEuclidean n j ∈ E})
      (𝓝 L)

/-- Definition 6.10: `f` is continuously differentiable on `E` if `E` consists of interior points
and for each coordinate direction `j`, there is a map `gⱼ : ℝⁿ → ℝᵐ` that is continuous on `E`
and satisfies `gⱼ x = ∂f/∂xⱼ (x)` for every `x ∈ E` in the within-`E` sense (using equation 6.u77);
the companion declarations below encode equations 6.u78–6.u80. -/
def ContinuouslyDifferentiableWithinOn
    {n m : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) : Prop :=
  E ⊆ interior E ∧
    ∀ j : Fin n,
      ∃ g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m),
        (∀ x, x ∈ E → HasPartialDerivWithinAt E f x j (g x)) ∧ ContinuousOn g E

/-- Definition 6.11: Let `E ⊆ ℝⁿ`, `f : ℝⁿ → ℝᵐ` (an ambient extension of a map on `E`), and
`x₀ ∈ E` such that for every coordinate `j` the partial derivative of `f` at `x₀` within `E`
exists. The derivative (Jacobian) matrix `Df(x₀)` is the `m × n` matrix whose `(i,j)`-entry is
`∂fᵢ/∂xⱼ (x₀)`. -/
noncomputable def derivativeMatrixWithinAt
    {n m : ℕ}
    (E : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hpartial : x₀ ∈ E ∧ ∀ j : Fin n,
      ∃ L : EuclideanSpace ℝ (Fin m), HasPartialDerivWithinAt E f x₀ j L) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => (Classical.choose (hpartial.2 j)) i

/-- For vector-valued maps, the partial derivative in one coordinate direction is determined by
the partial derivatives of the component functions `fun x => (f x) k` (equation 6.u78). -/
theorem hasPartialDerivWithinAt_componentwise
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {j : Fin n}
    {L : EuclideanSpace ℝ (Fin m)}
    :
    HasPartialDerivWithinAt E f x₀ j L ↔
    x₀ ∈ interior E ∧
      ∀ k : Fin m,
        Filter.Tendsto
          (fun t : ℝ =>
            t⁻¹ *
              (((fun x : EuclideanSpace ℝ (Fin n) => (f x) k)
                  (x₀ + t • standardBasisVectorEuclidean n j)) -
                ((fun x : EuclideanSpace ℝ (Fin n) => (f x) k) x₀)))
          (nhdsWithin (0 : ℝ)
            {t : ℝ |
              t ≠ 0 ∧ x₀ + t • standardBasisVectorEuclidean n j ∈ E})
          (𝓝 (L k)) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ
    intro k
    have hk :
        Filter.Tendsto
          (fun t : ℝ => (e (partialDifferenceQuotientWithin f x₀ j t)) k)
          (nhdsWithin (0 : ℝ)
            {t : ℝ |
              t ≠ 0 ∧ x₀ + t • standardBasisVectorEuclidean n j ∈ E})
          (𝓝 ((e L) k)) :=
      (tendsto_pi_nhds.1 ((e.continuous.tendsto L).comp h.2)) k
    simpa [partialDifferenceQuotientWithin, smul_eq_mul, e] using hk
  · intro h
    refine ⟨h.1, ?_⟩
    let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ
    have hk :
        ∀ k : Fin m,
          Filter.Tendsto
            (fun t : ℝ => (e (partialDifferenceQuotientWithin f x₀ j t)) k)
            (nhdsWithin (0 : ℝ)
              {t : ℝ |
                t ≠ 0 ∧ x₀ + t • standardBasisVectorEuclidean n j ∈ E})
            (𝓝 ((e L) k)) := by
      intro k
      have hk' := h.2 k
      simpa [partialDifferenceQuotientWithin, smul_eq_mul, e] using hk'
    have hpi :
        Filter.Tendsto
          (fun t : ℝ => e (partialDifferenceQuotientWithin f x₀ j t))
          (nhdsWithin (0 : ℝ)
            {t : ℝ |
              t ≠ 0 ∧ x₀ + t • standardBasisVectorEuclidean n j ∈ E})
          (𝓝 (e L)) :=
      tendsto_pi_nhds.2 hk
    exact (e.symm.continuous.tendsto (e L)).comp hpi

/-- If `f` has Fréchet derivative `f'` at `x₀` within `E`, then its `j`-th partial derivative at
`x₀` exists and equals `f' e_j`. -/
theorem hasFDerivWithinAt_hasPartialDerivWithinAt
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (j : Fin n) :
    HasPartialDerivWithinAt E f x₀ j
      (f' (standardBasisVectorEuclidean n j)) := by
  refine ⟨hx₀, ?_⟩
  simpa [partialDifferenceQuotientWithin] using
    (hasDirectionalDerivWithinAt_eq_fderiv
      (x₀ := x₀)
      (v := standardBasisVectorEuclidean n j)
      (f' := f')
      hx₀
      hfd)

/-- If `f` has ambient Fréchet derivative `f'` at `x₀`, then at an interior point of `E` its
`j`-th partial derivative within `E` exists and equals `f' e_j` (equation 6.u79). -/
theorem hasFDerivAt_hasPartialDerivWithinAt
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivAt f f' x₀)
    (j : Fin n) :
    HasPartialDerivWithinAt E f x₀ j
      (f' (standardBasisVectorEuclidean n j)) := by
  exact hasFDerivWithinAt_hasPartialDerivWithinAt hx₀ hfd.hasFDerivWithinAt j

/-- A linear derivative map sends a direction `v = ∑ⱼ vⱼ eⱼ` to
`∑ⱼ vⱼ (f' eⱼ)`, matching the directional derivative expansion by partial derivatives. -/
theorem fderiv_apply_eq_sum_standardBasis
    {n m : ℕ}
    (f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (v : EuclideanSpace ℝ (Fin n)) :
    f' v = ∑ j : Fin n, v j • f' (standardBasisVectorEuclidean n j) := by
  calc
    f' v = f' (∑ j : Fin n, v j • standardBasisVectorEuclidean n j) := by
      congr 1
      symm
      simpa [standardBasisVectorEuclidean] using
        (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
    _ = ∑ j : Fin n, f' (v j • standardBasisVectorEuclidean n j) := by
      rw [map_sum]
    _ = ∑ j : Fin n, v j • f' (standardBasisVectorEuclidean n j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [ContinuousLinearMap.map_smul]

/-- If `f` has Fréchet derivative within `E` at `x₀`, and if `L j` are the corresponding
partial derivatives at `x₀`, then the directional derivative in any direction `v` equals
`∑ⱼ vⱼ • L j` (equation 6.u80). -/
theorem hasFDerivWithinAt_directionalDeriv_eq_sum_partial
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    (hx₀ : x₀ ∈ interior E)
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hfd : HasFDerivWithinAt f f' E x₀)
    (L : Fin n → EuclideanSpace ℝ (Fin m))
    (hpartial : ∀ j : Fin n, HasPartialDerivWithinAt E f x₀ j (L j))
    (v : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 (∑ j : Fin n, v j • L j)) := by
  have hdir :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
        (𝓝 (f' v)) :=
    hasDirectionalDerivWithinAt_eq_fderiv
      (x₀ := x₀)
      (v := v)
      (f' := f')
      hx₀
      hfd
  have hL :
      ∀ j : Fin n, L j = f' (standardBasisVectorEuclidean n j) := by
    intro j
    let e_j : EuclideanSpace ℝ (Fin n) := standardBasisVectorEuclidean n j
    let g : ℝ → EuclideanSpace ℝ (Fin m) := fun t : ℝ => f (x₀ + t • e_j)
    let s : Set ℝ := (fun t : ℝ => x₀ + t • e_j) ⁻¹' E
    have hset :
        {t : ℝ | t ≠ 0 ∧ x₀ + t • e_j ∈ E} = s \ ({0} : Set ℝ) := by
      ext t
      simp [s, and_comm]
    have hslope_eq :
        slope g 0 = partialDifferenceQuotientWithin f x₀ j := by
      ext t
      by_cases ht : t = 0
      · subst ht
        simp [slope, g, partialDifferenceQuotientWithin, e_j]
      · simp [slope, g, partialDifferenceQuotientWithin, e_j]
    have hslopeL :
        Filter.Tendsto
          (slope g 0)
          (nhdsWithin (0 : ℝ) (s \ ({0} : Set ℝ)))
          (𝓝 (L j)) := by
      have hslopeL' :
          Filter.Tendsto
            (slope g 0)
            (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • e_j ∈ E})
            (𝓝 (L j)) := by
        simpa [hslope_eq] using (hpartial j).2
      simpa [hset] using hslopeL'
    have hderivWithinL : HasDerivWithinAt g (L j) s 0 :=
      (hasDerivWithinAt_iff_tendsto_slope).2 hslopeL
    have hderivWithinF : HasDerivWithinAt g (f' e_j) s 0 := by
      simpa [HasLineDerivWithinAt, g, s] using hfd.hasLineDerivWithinAt e_j
    have hE : E ∈ 𝓝 x₀ := mem_interior_iff_mem_nhds.mp hx₀
    have hE0 : E ∈ 𝓝 (x₀ + (0 : ℝ) • e_j) := by
      simpa using hE
    have hs_mem : s ∈ 𝓝 (0 : ℝ) := by
      have hcont : ContinuousAt (fun t : ℝ => x₀ + t • e_j) 0 := by
        simpa [e_j] using
          (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      simpa [s] using hcont.preimage_mem_nhds hE0
    have hderivAtL : HasDerivAt g (L j) 0 := hderivWithinL.hasDerivAt hs_mem
    have hderivAtF : HasDerivAt g (f' e_j) 0 := hderivWithinF.hasDerivAt hs_mem
    exact HasDerivAt.unique hderivAtL hderivAtF
  have hsum :
      (∑ j : Fin n, v j • L j) = f' v := by
    calc
      ∑ j : Fin n, v j • L j = ∑ j : Fin n, v j • f' (standardBasisVectorEuclidean n j) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hL j]
      _ = f' v := by
        symm
        exact fderiv_apply_eq_sum_standardBasis f' v
  simpa [hsum] using hdir

/-- Proposition 6.9: Let `E ⊆ ℝⁿ`, `f : ℝⁿ → ℝᵐ`, and `x₀ ∈ E`.
Assume `f` is differentiable at `x₀` within `E` with derivative `f'`, and let
`Df` be the Jacobian matrix representing `f'` (so `f' = Matrix.mulVecLin Df`).
Then for every direction `v`, the directional derivative exists and
`(Dᵥ f(x₀))ᵀ = Df * vᵀ`, i.e. the directional derivative limit is `Matrix.mulVec Df v`.
Equivalently, `Dᵥ f(x₀) = f' v = ∑ⱼ vⱼ • (f' eⱼ)`. -/
theorem directionalDerivWithinAt_eq_jacobian_mulVec_and_sum
    {n m : ℕ}
    {E : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
    {x₀ : EuclideanSpace ℝ (Fin n)}
    {f' : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)}
    (hx₀ : x₀ ∈ E)
    (hfd : HasFDerivWithinAt f f' E x₀)
    (Df : Matrix (Fin m) (Fin n) ℝ)
    (hDf :
      ∀ w : EuclideanSpace ℝ (Fin n),
        f' w =
          (EuclideanSpace.equiv (Fin m) ℝ).symm
            (Matrix.mulVec Df ((EuclideanSpace.equiv (Fin n) ℝ) w)))
    (v : EuclideanSpace ℝ (Fin n)) :
    Filter.Tendsto
      (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
      (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
      (𝓝 ((EuclideanSpace.equiv (Fin m) ℝ).symm
        (Matrix.mulVec Df ((EuclideanSpace.equiv (Fin n) ℝ) v)))) ∧
      (EuclideanSpace.equiv (Fin m) ℝ).symm
        (Matrix.mulVec Df ((EuclideanSpace.equiv (Fin n) ℝ) v)) = f' v ∧
      f' v = ∑ j : Fin n, v j • f' (standardBasisVectorEuclidean n j) := by
  let _ := hx₀
  have hline :
      HasDerivWithinAt (fun t : ℝ => f (x₀ + t • v)) (f' v)
        ((fun t : ℝ => x₀ + t • v) ⁻¹' E) 0 := by
    simpa [HasLineDerivWithinAt] using hfd.hasLineDerivWithinAt v
  have hslope :
      Filter.Tendsto (slope (fun t : ℝ => f (x₀ + t • v)) 0)
        (nhdsWithin (0 : ℝ) (((fun t : ℝ => x₀ + t • v) ⁻¹' E) \ ({0} : Set ℝ)))
        (𝓝 (f' v)) :=
    (hasDerivWithinAt_iff_tendsto_slope).1 hline
  have hset :
      (((fun t : ℝ => x₀ + t • v) ⁻¹' E) \ ({0} : Set ℝ)) =
        {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E} := by
    ext t
    simp [and_comm]
  have hslope' :
      Filter.Tendsto (slope (fun t : ℝ => f (x₀ + t • v)) 0)
        (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
        (𝓝 (f' v)) := by
    simpa [hset] using hslope
  have hfun :
      slope (fun t : ℝ => f (x₀ + t • v)) 0 =
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀)) := by
    ext t
    by_cases ht : t = 0
    · subst ht
      simp [slope]
    · simp [slope]
  have hdir :
      Filter.Tendsto
        (fun t : ℝ => t⁻¹ • (f (x₀ + t • v) - f x₀))
        (nhdsWithin (0 : ℝ) {t : ℝ | t ≠ 0 ∧ x₀ + t • v ∈ E})
        (𝓝 (f' v)) := by
    simpa [hfun] using hslope'
  have hsum :
      f' v = ∑ j : Fin n, v j • f' (standardBasisVectorEuclidean n j) :=
    fderiv_apply_eq_sum_standardBasis f' v
  refine ⟨?_, (hDf v).symm, hsum⟩
  simpa [hDf v] using hdir


end Section03
end Chap06
