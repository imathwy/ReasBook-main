import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Algebra.DirectSum.Module

open scoped Manifold Topology

noncomputable section

-- Domain sampling pass: `ModelWithCorners.pi` is the canonical finite-product manifold owner, and
-- `DirectSum.linearEquivFunOnFintype` converts the tangent-space `Π`-model into Lee's finite
-- direct-sum presentation. The source formula is the componentwise `mfderiv` of the projections.

section

universe uE uH uM

variable {k : ℕ}
variable {E : Fin k → Type uE} [∀ j, NormedAddCommGroup (E j)] [∀ j, NormedSpace ℝ (E j)]
variable {H : Fin k → Type uH} [∀ j, TopologicalSpace (H j)]
variable {I : (j : Fin k) → ModelWithCorners ℝ (E j) (H j)}
variable {M : Fin k → Type uM} [∀ j, TopologicalSpace (M j)] [∀ j, ChartedSpace (H j) (M j)]

/-- The canonical finite-product tangent-space equivalence from Proposition 3.14: for manifolds
indexed by `Fin k`, the tangent space at `p` is canonically linearly equivalent to the direct sum
of the tangent spaces of the factors. Via `DirectSum.linearEquivFunOnFintype`, this is the map
whose `j`-th component is the differential of the `j`-th projection. Because the models `I j` are
arbitrary real `ModelWithCorners`, this also covers the source's variant where one factor is a
manifold with boundary. -/
def tangentSpaceFiniteProductEquivDirectSum (p : ∀ j : Fin k, M j) :
    TangentSpace (ModelWithCorners.pi I) p ≃ₗ[ℝ]
      DirectSum (Fin k) (fun j ↦ TangentSpace (I j) (p j)) :=
  (DirectSum.linearEquivFunOnFintype ℝ (Fin k) (fun j ↦ TangentSpace (I j) (p j))).symm

/-- Helper for Proposition 3.14: a point lies in the range of `ModelWithCorners.pi I` exactly when
each coordinate lies in the range of the corresponding factor model. -/
lemma mem_range_modelWithCornersPi_iff {y : ∀ j : Fin k, E j} :
    y ∈ Set.range (ModelWithCorners.pi I) ↔ ∀ j, y j ∈ Set.range (I j) := by
  constructor
  · rintro ⟨x, rfl⟩ j
    exact ⟨x j, rfl⟩
  · intro hy
    choose x hx using hy
    refine ⟨x, ?_⟩
    ext j
    exact hx j

/-- Helper for Proposition 3.14: the product chart target is the product of the factor chart
targets. -/
lemma mem_piChartAt_target_iff (p : ∀ j : Fin k, M j) {y : ∀ j : Fin k, E j} :
    (ModelWithCorners.pi I).symm y ∈ (chartAt (H := ModelPi H) p).target ↔
      ∀ j, (I j).symm (y j) ∈ (chartAt (H j) (p j)).target := by
  -- The chart of a finite product is the product of the factor charts.
  constructor
  · intro hy j
    simpa [piChartedSpace_chartAt, ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using
      hy j (by simp)
  · intro hy j hj
    simpa [piChartedSpace_chartAt, ModelWithCorners.pi, PartialEquiv.pi_symm_apply] using hy j

/-- Helper for Proposition 3.14: the target of the finite-product extended chart is the
coordinatewise product of the factor extended-chart targets. -/
lemma mem_extChartAt_pi_target_iff (p : ∀ j : Fin k, M j) {y : ∀ j : Fin k, E j} :
    y ∈ (extChartAt (ModelWithCorners.pi I) p).target ↔
      ∀ j, y j ∈ (extChartAt (I j) (p j)).target := by
  -- Combine the product-chart target description with the coordinatewise range description.
  rw [extChartAt_target]
  constructor
  · rintro ⟨hyChart, hyRange⟩ j
    have hyChartj : (I j).symm (y j) ∈ (chartAt (H j) (p j)).target :=
      (mem_piChartAt_target_iff (I := I) p).1 hyChart j
    have hyRangej : y j ∈ Set.range (I j) :=
      (mem_range_modelWithCornersPi_iff (I := I)).1 hyRange j
    simpa [extChartAt_target] using And.intro hyRangej hyChartj
  · intro hy
    refine ⟨(mem_piChartAt_target_iff (I := I) p).2 ?_,
      (mem_range_modelWithCornersPi_iff (I := I)).2 ?_⟩
    · intro j
      exact (hy j).2
    · intro j
      simpa using (hy j).1

/-- Helper for Proposition 3.14: the inverse of the finite-product extended chart acts
coordinatewise on each factor. -/
lemma extChartAt_pi_symm_apply (p : ∀ j : Fin k, M j) (y : ∀ j : Fin k, E j) (j : Fin k) :
    ((extChartAt (ModelWithCorners.pi I) p).symm y) j =
      (extChartAt (I j) (p j)).symm (y j) := by
  -- The product chart inverse is just the product of the factor chart inverses.
  rfl

/-- Helper for Proposition 3.14: the finite-product extended chart sends `p` to the tuple of its
factor extended-chart coordinates. -/
lemma extChartAt_pi_apply (p : ∀ j : Fin k, M j) (j : Fin k) :
    extChartAt (ModelWithCorners.pi I) p p j = extChartAt (I j) (p j) (p j) := by
  -- The forward finite-product chart is coordinatewise as well.
  rfl

/-- Helper for Proposition 3.14: the `j`-th coordinate projection on a finite product manifold has
manifold derivative `ContinuousLinearMap.proj j`. -/
lemma hasMFDerivAt_piProjection (p : ∀ j : Fin k, M j) (j : Fin k) :
    HasMFDerivAt (ModelWithCorners.pi I) (I j) (fun x : ∀ l : Fin k, M l ↦ x j) p
      (ContinuousLinearMap.proj j) := by
  -- Reduce the manifold derivative to the Fréchet derivative of evaluation in product charts.
  refine ⟨continuous_apply j |>.continuousAt, ?_⟩
  have hChart :
      ∀ᶠ y in 𝓝[Set.range (ModelWithCorners.pi I)] extChartAt (ModelWithCorners.pi I) p p,
        (extChartAt (I j) (p j) ∘ (fun x : ∀ l : Fin k, M l ↦ x j) ∘
          (extChartAt (ModelWithCorners.pi I) p).symm) y = y j := by
    -- On the product chart target, the coordinate projection is literally evaluation at `j`.
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := ModelWithCorners.pi I) p] with y hy
    have hyj : y j ∈ (extChartAt (I j) (p j)).target :=
      (mem_extChartAt_pi_target_iff (I := I) p).1 hy j
    calc
      (extChartAt (I j) (p j) ∘ (fun x : ∀ l : Fin k, M l ↦ x j) ∘
          (extChartAt (ModelWithCorners.pi I) p).symm) y
          = extChartAt (I j) (p j) (((extChartAt (ModelWithCorners.pi I) p).symm y) j) := rfl
      _ = extChartAt (I j) (p j) ((extChartAt (I j) (p j)).symm (y j)) := by
        rw [extChartAt_pi_symm_apply (I := I)]
      _ = y j := (extChartAt (I j) (p j)).right_inv hyj
  apply HasFDerivWithinAt.congr_of_eventuallyEq
    (hasFDerivWithinAt_apply j (extChartAt (ModelWithCorners.pi I) p p)
      (Set.range (ModelWithCorners.pi I)))
    hChart
  -- Evaluate the chart identity at the basepoint and cancel the `j`-th coordinate chart.
  rw [extChartAt_pi_apply (I := I)]
  exact (extChartAt (I j) (p j)).right_inv <|
    (extChartAt (I j) (p j)).map_source (mem_extChartAt_source (I := I j) (p j))

/-- Helper for Proposition 3.14: the manifold derivative of the `j`-th coordinate projection is
the coordinate projection on tangent spaces. -/
@[simp, mfld_simps]
lemma mfderiv_piProjection (p : ∀ j : Fin k, M j) (j : Fin k) :
    mfderiv (ModelWithCorners.pi I) (I j) (fun x : ∀ l : Fin k, M l ↦ x j) p =
      ContinuousLinearMap.proj j :=
  (hasMFDerivAt_piProjection (I := I) p j).mfderiv

/-- Helper for Proposition 3.14: converting the canonical direct-sum tangent vector back to a
coordinate tuple recovers the original tangent vector. -/
lemma tangentSpaceFiniteProductEquivDirectSum_toFun (p : ∀ j : Fin k, M j)
    (v : TangentSpace (ModelWithCorners.pi I) p) :
    DirectSum.linearEquivFunOnFintype ℝ (Fin k) (fun j ↦ TangentSpace (I j) (p j))
      (tangentSpaceFiniteProductEquivDirectSum p v) = v := by
  -- Route correction: cancel the direct-sum/function equivalence before taking coordinates.
  rw [tangentSpaceFiniteProductEquivDirectSum]
  exact (DirectSum.linearEquivFunOnFintype ℝ (Fin k)
    (fun j ↦ TangentSpace (I j) (p j))).apply_symm_apply v

/-- Proposition 3.14: under the canonical `DirectSum`-to-`Π` identification, the components of
`tangentSpaceFiniteProductEquivDirectSum p` are the differentials of the coordinate projections. -/
theorem tangentSpaceFiniteProductEquivDirectSum_apply (p : ∀ j : Fin k, M j)
    (v : TangentSpace (ModelWithCorners.pi I) p) (j : Fin k) :
    (DirectSum.linearEquivFunOnFintype ℝ (Fin k) (fun j ↦ TangentSpace (I j) (p j))
      (tangentSpaceFiniteProductEquivDirectSum p v)) j =
      mfderiv (ModelWithCorners.pi I) (I j) (fun x : ∀ l : Fin k, M l ↦ x j) p v := by
  -- Route correction: read off the `j`-th coordinate only after the function-level cancellation.
  have hCoordinate :
      (DirectSum.linearEquivFunOnFintype ℝ (Fin k) (fun j ↦ TangentSpace (I j) (p j))
        (tangentSpaceFiniteProductEquivDirectSum p v)) j = v j := by
    simpa using congrArg (fun f ↦ f j)
      (tangentSpaceFiniteProductEquivDirectSum_toFun (I := I) p v)
  -- Rewrite the manifold derivative of the projection to the linear coordinate projection.
  rw [mfderiv_piProjection]
  simpa [ContinuousLinearMap.proj_apply] using hCoordinate

end
