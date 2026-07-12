import Mathlib
import SmoothManifolds_Lee_2012.Chap02.Sec02_09.Example_2_14
import SmoothManifolds_Lee_2012.Chap03.Sec03_14.Proposition_3_9
import SmoothManifolds_Lee_2012.Chap03.Sec03_16.Proposition_3_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe uH uM

-- Domain sampling pass:
-- * primary domain: smooth sections of the tangent bundle, expressed in chart coordinates;
-- * core/canonical owner for tangent-bundle sections:
--   `Bundle.Trivialization.contMDiffOn_section_baseSet_iff`;
-- * preferred tangent-bundle trivialization owner: `trivializationAt` /
--   `TangentBundle.trivializationAt_apply`;
-- * componentwise Euclidean smoothness owner: `contMDiffOn_pi_space`.
-- Primitive data is only the section `X : ∀ p, TangentSpace I p`. The chart-side Euclidean map
-- and its scalar components are derived views, so this file keeps them only on theorem surfaces and
-- does not introduce parallel public owners for them.

variable {n : ℕ}
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable [IsManifold I (∞ : ℕ∞ω) M]

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: on an open set, ambient smoothness is equivalent to smoothness of
the restricted map on the corresponding open subtype. -/
private lemma contMDiffOn_iff_contMDiff_restrict
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold J (∞ : ℕ∞ω) M']
    (U : TopologicalSpace.Opens M) (f : M → M') :
    ContMDiffOn I J ∞ f U ↔ ContMDiff I J ∞ (fun x : U ↦ f x) := by
  constructor
  · intro hf x
    -- Upgrade smoothness on the open set to ambient smoothness at `x`, then reinterpret it on the
    -- corresponding open subtype.
    have hxWithin : ContMDiffWithinAt I J ∞ f (U : Set M) x := hf x x.2
    have hxAt : ContMDiffAt I J ∞ f x := by
      exact hxWithin.contMDiffAt (U.2.mem_nhds x.2)
    exact (contMDiffAt_subtype_iff (U := U) (f := f) (x := x)).2 hxAt
  · intro hf x hx
    -- Conversely, read the restricted smoothness at `⟨x, hx⟩` as ambient smoothness at `x` and
    -- then restrict back to the open set.
    let xU : U := ⟨x, hx⟩
    have hxAt : ContMDiffAt I J ∞ f x := by
      exact (contMDiffAt_subtype_iff (U := U) (f := f) (x := xU)).1 (hf xU)
    exact hxAt.contMDiffWithinAt

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: the derivative of a `C^∞` diffeomorphism is invertible at every
point. -/
private lemma diffeomorph_mfderiv_isInvertible
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold J (∞ : ℕ∞ω) M']
    (F : M ≃ₘ⟮I, J⟯ M') (x : M) :
    (mfderiv I J F x).IsInvertible := by
  -- Package the derivative as the canonical linear equivalence supplied by the diffeomorphism API.
  let e := F.mfderivToContinuousLinearEquiv (by simp) x
  refine ⟨e, ?_⟩
  simpa [e] using
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := F) (hn := by simp) (x := x)).symm

/-- Helper for Proposition 8.1: the chart and its inverse are smooth between the source and target
open subtypes already under the current `C^∞` maximal-atlas hypothesis. -/
private def chartSourceTargetDiffeomorph
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M) :
    (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) ≃ₘ⟮I, I⟯
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) where
  toEquiv := e.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    intro x
    let f : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) →
        (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) := fun x ↦
      show (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) from
        e.toHomeomorphSourceTarget x
    -- Coerce away the target subtype so the goal matches the ambient chart map.
    refine (ContMDiffAt.subtypeVal_comp_iff
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) f x).1 ?_
    refine (contMDiffAt_subtype_iff
      (U := (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M))
      (f := fun x : M ↦ e x) (x := x)).2 ?_
    simpa using
      (contMDiffAt_of_mem_maximalAtlas
        (I := I) (n := (∞ : ℕ∞ω)) (e := e) he x.2)
  contMDiff_invFun := by
    intro y
    let f : (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H) →
        (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) := fun y ↦
      show (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) from
        e.toHomeomorphSourceTarget.symm y
    -- Coerce away the source subtype so the goal matches the ambient inverse chart map.
    refine (ContMDiffAt.subtypeVal_comp_iff
      (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M) f y).1 ?_
    refine (contMDiffAt_subtype_iff
      (U := (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H))
      (f := fun y : H ↦ e.symm y) (x := y)).2 ?_
    simpa using
      (contMDiffAt_symm_of_mem_maximalAtlas
        (I := I) (n := (∞ : ℕ∞ω)) (e := e) he y.2)

/-- Helper for Proposition 8.1: the forward map of `chartSourceTargetDiffeomorph` is the
homeomorphism induced by the chart. -/
private lemma chartSourceTargetDiffeomorph_apply
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    (x : (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens M)) :
    chartSourceTargetDiffeomorph (I := I) e he x = e.toHomeomorphSourceTarget x := rfl

/-- Helper for Proposition 8.1: the extended chart is manifold-differentiable at every point of
its source. -/
private lemma mdifferentiableAt_extend
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    {x : M} (hx : x ∈ e.source) :
    MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) x := by
  -- The extended chart is smooth on its source because `e` belongs to the maximal atlas.
  exact (contMDiffAt_extend (I := I) (n := (∞ : ℕ∞ω)) he hx).mdifferentiableAt (by simp)

/-- Helper for Proposition 8.1: the inverse extended chart is manifold-differentiable within its
natural target. -/
private lemma mdifferentiableWithinAt_extend_symm
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (e.extend I).target) :
    MDifferentiableWithinAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) I
      (e.extend I).symm (e.extend I).target y := by
  -- The inverse extended chart is smooth on the full chart target.
  have hy' : y ∈ I '' e.target := by
    rwa [OpenPartialHomeomorph.extend_target'] at hy
  convert
      (contMDiffOn_extend_symm (I := I) (n := (∞ : ℕ∞ω)) he y hy').mdifferentiableWithinAt
        (by simp) using 1
  rw [OpenPartialHomeomorph.extend_target']

omit [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: the natural target of `e.extend I` has the unique differential
property inherited from `Set.range I`. -/
private lemma uniqueMDiffOn_extendTarget
    (e : OpenPartialHomeomorph M H) :
    UniqueMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I).target := by
  let u : Set (EuclideanSpace ℝ (Fin n)) := I.symm ⁻¹' e.target
  have hu : IsOpen u := e.open_target.preimage I.continuous_symm
  -- The chart target is an open subset of `Set.range I`, where the model space already has the
  -- unique differential property.
  simpa [u, OpenPartialHomeomorph.extend_target, Set.inter_assoc, Set.inter_left_comm,
    Set.inter_comm] using
    (ModelWithCorners.uniqueMDiffOn I).inter hu

/-- Helper for Proposition 8.1: on the model space, smoothness of a vector field is equivalent to
smoothness of its Euclidean coordinate map. -/
private lemma smoothModelVectorField_iff_smoothCoordinates
    (s : Set (EuclideanSpace ℝ (Fin n)))
    (Y : ∀ y : EuclideanSpace ℝ (Fin n),
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n))).tangent ∞ (T% Y) s ↔
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun y ↦ NormedSpace.fromTangentSpace y (Y y)) s := by
  let e0 := trivializationAt (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (0 : EuclideanSpace ℝ (Fin n))
  constructor
  · intro h x hx
    have hxbase : x ∈ e0.baseSet := by
      simp [e0]
    -- On the model space, the tangent-bundle trivialization records exactly the underlying vector.
    have hx' :=
      (Bundle.Trivialization.contMDiffWithinAt_section
        (IB := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (e := e0) (a := s) (x₀ := x) hxbase).1
        (h x hx)
    simpa [e0, trivializationAt_model_space_apply, NormedSpace.fromTangentSpace]
      using hx'
  · intro h x hx
    have hxbase : x ∈ e0.baseSet := by
      simp [e0]
    -- The converse uses the same model-space trivialization, now rebuilding the section.
    have hx' :=
      (Bundle.Trivialization.contMDiffWithinAt_section
        (IB := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (e := e0) (a := s) (x₀ := x) hxbase).2
        (by
          simpa [e0, trivializationAt_model_space_apply,
            NormedSpace.fromTangentSpace] using h x hx)
    exact hx'

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: pushing the pullback field along an open inclusion recovers the
original ambient vector field. -/
private lemma tangentMap_subtype_val_pullback_eq
    (U : TopologicalSpace.Opens M)
    (X : ∀ p : M, TangentSpace I p)
    (p : U) :
    tangentMap I I (Subtype.val : U → M)
      (T% (VectorField.mpullback I I (Subtype.val : U → M) X) p) =
      T% X p.1 := by
  -- The restricted field was defined using the inverse derivative of the open inclusion.
  simp only [tangentMap, VectorField.mpullback_apply, Bundle.TotalSpace.mk_inj]
  exact (mfderiv_open_subset_inclusion_isInvertible (I := I) U p).self_apply_inverse (X p.1)

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: pulling back a vector field by the inverse of a diffeomorphism
pushes vectors forward by the original derivative. -/
private lemma mpullback_diffeomorph_symm_apply
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold J (∞ : ℕ∞ω) M']
    (F : M ≃ₘ⟮I, J⟯ M')
    (X : ∀ p : M, TangentSpace I p)
    (p : M) :
    VectorField.mpullback J I F.symm X (F p) = mfderiv I J F p (X p) := by
  -- Rewrite the pullback using the inverse derivative, then differentiate `F.symm ∘ F = id`.
  rw [VectorField.mpullback_apply, F.symm_apply_apply]
  let e := F.symm.mfderivToContinuousLinearEquiv (by simp) (F p)
  have hcoe :
      ↑(F.symm.mfderivToContinuousLinearEquiv (by simp) (F p)) =
        mfderiv J I F.symm (F p) :=
    F.symm.mfderivToContinuousLinearEquiv_coe (by simp) (x := F p)
  refine
    (ContinuousLinearMap.IsInvertible.inverse_apply_eq
      ⟨e, by
        simpa [e] using hcoe.symm⟩).2 ?_
  have hcomp :
      mfderiv I I (F.symm ∘ F) p (X p) =
        mfderiv J I F.symm (F p) (mfderiv I J F p (X p)) := by
    exact mfderiv_comp_apply
      (x := p)
      (g := F.symm)
      (f := F)
      (F.symm.contMDiff.mdifferentiableAt (by simp))
      (F.contMDiff.mdifferentiableAt (by simp))
      (X p)
  have hcomp' :
      mfderiv I I (fun x : M ↦ F.symm (F x)) p (X p) =
        mfderiv J I F.symm (F p) (mfderiv I J F p (X p)) := by
    simpa [Function.comp] using hcomp
  have hid : (fun x : M ↦ F.symm (F x)) = id := by
    funext x
    simp
  rw [hid, mfderiv_id] at hcomp'
  simpa using hcomp'

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: pulling back by a diffeomorphism and then by its inverse returns
the original vector field. -/
private lemma mpullback_diffeomorph_cancel
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'}
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold J (∞ : ℕ∞ω) M']
    (F : M ≃ₘ⟮I, J⟯ M')
    (X : ∀ p : M, TangentSpace I p) :
    VectorField.mpullback I J F (VectorField.mpullback J I F.symm X) = X := by
  funext p
  -- The inner pullback creates the pushed-forward vector at `F p`, and the outer pullback then
  -- inverts the same derivative.
  rw [VectorField.mpullback_apply]
  have hpush := mpullback_diffeomorph_symm_apply (I := I) (J := J) F X p
  let e := F.mfderivToContinuousLinearEquiv (by simp) p
  have hcoe :
      ↑(F.mfderivToContinuousLinearEquiv (by simp) p) = mfderiv I J F p :=
    F.mfderivToContinuousLinearEquiv_coe (by simp) (x := p)
  exact
    (ContinuousLinearMap.IsInvertible.inverse_apply_eq
      ⟨e, by
        simpa [e] using hcoe.symm⟩).2 hpush

/-- Helper for Proposition 8.1: smoothness of a vector field on the chart source is equivalent to
smoothness of its pullback to the source open subtype. -/
private lemma smoothOnSource_iff_smoothRestrictedVectorField
    (e : OpenPartialHomeomorph M H)
    (X : ∀ p : M, TangentSpace I p) :
    let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
    let XU : ∀ p : U, TangentSpace I p :=
      VectorField.mpullback I I (Subtype.val : U → M) X
    ContMDiffOn I I.tangent ∞ (T% X) e.source ↔
      ContMDiff I I.tangent ∞ (T% XU) := by
  let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
  let XU : ∀ p : U, TangentSpace I p :=
    VectorField.mpullback I I (Subtype.val : U → M) X
  letI : ChartedSpace H U := inferInstance
  letI : IsManifold I (∞ : ℕ∞ω) U := inferInstance
  letI : IsManifold I 1 U := inferInstance
  constructor
  · intro hX
    -- Restrict the ambient smooth field to the open subtype by pulling it back along the inclusion.
    have hpull :=
      hX.mpullback_vectorField_preimage
        (f := (Subtype.val : U → M))
        (hf := (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)))
        (hf' := by
          intro p hp
          simpa using mfderiv_open_subset_inclusion_isInvertible (I := I) U p)
        (hmn := by simp)
    have hpull' :
        ContMDiffOn I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (fun p : U ↦
            (show TangentBundle I U from ⟨p, XU p⟩))
          (Set.univ : Set U) := by
      convert hpull using 1
      ext p
      simp [U]
    have hcont :
        ContMDiff I (I.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
          (fun p : U ↦
            (show TangentBundle I U from ⟨p, XU p⟩)) :=
      (contMDiffOn_univ).1 hpull'
    simpa [XU] using hcont
  · intro hXU
    -- Rebuild the ambient section on `e.source` by postcomposing the restricted section with the
    -- tangent map of the open inclusion.
    have hinc :
        ContMDiff I.tangent I.tangent ∞ (tangentMap I I (Subtype.val : U → M)) := by
      exact
        (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)).contMDiff_tangentMap
          (m := ∞) (by simp)
    have hcomp :
        ContMDiff I I.tangent ∞
          (fun p : U ↦ tangentMap I I (Subtype.val : U → M) (T% XU p)) :=
      hinc.comp hXU
    have hEq :
        (fun p : U ↦ tangentMap I I (Subtype.val : U → M) (T% XU p)) =
          fun p : U ↦ T% X p.1 := by
      funext p
      simpa [XU] using tangentMap_subtype_val_pullback_eq (I := I) U X p
    have hrest : ContMDiff I I.tangent ∞ (fun p : U ↦ T% X p.1) := by
      simpa [hEq] using hcomp
    exact (contMDiffOn_iff_contMDiff_restrict (I := I) (J := I.tangent) U (T% X)).2 hrest

/-- Helper for Proposition 8.1: transporting the restricted vector field through the chart
diffeomorphism preserves smoothness. -/
private lemma smoothRestrictedVectorField_iff_smoothChartPullback
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    (X : ∀ p : M, TangentSpace I p) :
    let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
    let V : TopologicalSpace.Opens H := ⟨e.target, e.open_target⟩
    let XU : ∀ p : U, TangentSpace I p :=
      VectorField.mpullback I I (Subtype.val : U → M) X
    let F : U ≃ₘ⟮I, I⟯ V := chartSourceTargetDiffeomorph (I := I) e he
    let Y : ∀ q : V, TangentSpace I q := VectorField.mpullback I I F.symm XU
    ContMDiff I I.tangent ∞ (T% XU) ↔
      ContMDiff I I.tangent ∞ (T% Y) := by
  let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
  let V : TopologicalSpace.Opens H := ⟨e.target, e.open_target⟩
  let XU : ∀ p : U, TangentSpace I p :=
    VectorField.mpullback I I (Subtype.val : U → M) X
  let F : U ≃ₘ⟮I, I⟯ V := chartSourceTargetDiffeomorph (I := I) e he
  let Y : ∀ q : V, TangentSpace I q := VectorField.mpullback I I F.symm XU
  constructor
  · intro hXU
    -- Pull smoothness across the chart diffeomorphism from the source subtype to the target
    -- subtype.
    simpa [Y, F] using
      (ContMDiff.mpullback_vectorField
        (I := I) (I' := I)
        (f := F.symm)
        (V := XU)
        (m := ∞) (n := ∞)
        hXU
        F.symm.contMDiff
        (fun q ↦ diffeomorph_mfderiv_isInvertible (I := I) (J := I) F.symm q)
        (by simp))
  · intro hY
    -- Pull the transported field back through the inverse chart diffeomorphism and use
    -- diffeomorphic pullback cancellation to recover the restricted source field.
    have hpull :
        ContMDiff I I.tangent ∞ (T% (VectorField.mpullback I I F Y)) := by
      simpa [Y, F] using
        (ContMDiff.mpullback_vectorField
          (I := I) (I' := I)
          (f := F)
          (V := Y)
          (m := ∞) (n := ∞)
          hY
          F.contMDiff
          (fun p ↦ diffeomorph_mfderiv_isInvertible (I := I) (J := I) F p)
          (by simp))
    simpa [Y, F, mpullback_diffeomorph_cancel (I := I) (J := I) F XU] using hpull

/-- Helper for Proposition 8.1: on an open subset of the model space, the tangent-bundle
trivialization is the explicit chart-coordinate formula for tangent vectors. -/
private lemma openSubsetTrivializationAt_apply_eq_coordinate
    (U : TopologicalSpace.Opens H)
    (x y : U) (v : TangentSpace I y) :
    (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x
      (show TangentBundle I U from ⟨y, v⟩)).2 =
      NormedSpace.fromTangentSpace (I y)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) y v) := by
  have htriv :
      (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) x
        (show TangentBundle I U from ⟨y, v⟩)).2 = v := by
    have htoProd :=
      tangent_bundle_opens_trivializationAt_eq_toProd (I := I) (U := U) x
    -- Over an open subset of the model space, the tangent-bundle trivialization is the canonical
    -- product chart, so its second coordinate is exactly the tangent vector itself.
    simpa [Bundle.TotalSpace.toProd] using
      congrArg Prod.snd (congrArg (fun f => f (show TangentBundle I U from ⟨y, v⟩)) htoProd)
  have hchart : (extChartAt I y : U → EuclideanSpace ℝ (Fin n)) = fun r : U ↦ I r := by
    funext r
    -- On an open subset of the model space, the preferred chart is just the restricted inclusion
    -- followed by the ambient model map `I`.
    rw [extChartAt_coe]
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
    simp
  have hmfderiv :
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) y =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt I y) y := by
    exact mfderiv_congr (x := y) hchart.symm
  have hchartAt : extChartAt I y y = I y := by
    simpa using congrArg (fun f : U → EuclideanSpace ℝ (Fin n) ↦ f y) hchart
  have hcoord :
      NormedSpace.fromTangentSpace (I y)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) y v) = v := by
    -- The preferred chart on the open subset has identity derivative at its basepoint.
    rw [hmfderiv, mfderiv_extChartAt_self (I := I) (x := y)]
    change (ContinuousLinearMap.id ℝ (TangentSpace I y)) v = v
    exact ContinuousLinearMap.id_apply _
  -- Compare the trivialization coordinate with the explicit `mfderiv` formula through the same
  -- canonical open-subset coordinate identification.
  exact htriv.trans hcoord.symm

/-- Helper for Proposition 8.1: the chart-target coordinate map on an open subset of the model
space is the identity on tangent vectors. -/
private lemma openSubsetCoordinate_eq_self
    (U : TopologicalSpace.Opens H)
    (y : U) (v : TangentSpace I y) :
    NormedSpace.fromTangentSpace (I y)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) y v) = v := by
  have hchart : (extChartAt I y : U → EuclideanSpace ℝ (Fin n)) = fun r : U ↦ I r := by
    funext r
    -- On an open subset of the model space, the preferred chart is just the restricted inclusion
    -- followed by the ambient model map `I`.
    rw [extChartAt_coe]
    rw [TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq]
    simp
  have hmfderiv :
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) y =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (extChartAt I y) y := by
    exact mfderiv_congr (x := y) hchart.symm
  have hchartAt : extChartAt I y y = I y := by
    simpa using congrArg (fun f : U → EuclideanSpace ℝ (Fin n) ↦ f y) hchart
  -- The manifold derivative of the preferred chart at its basepoint is the identity.
  rw [hmfderiv, mfderiv_extChartAt_self (I := I) (x := y)]
  change (ContinuousLinearMap.id ℝ (TangentSpace I y)) v = v
  exact ContinuousLinearMap.id_apply _

/-- Helper for Proposition 8.1: on an open subset of the model space, a vector field is smooth
exactly when its explicit chart coordinates are smooth. -/
private lemma smoothOpenSubsetVectorField_iff_smoothCoordinates
    (U : TopologicalSpace.Opens H)
    (Y : ∀ q : U, TangentSpace I q) :
    ContMDiff I I.tangent ∞ (T% Y) ↔
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
        (fun q : U ↦ NormedSpace.fromTangentSpace (I q)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) q (Y q))) := by
  have hraw :
      ContMDiff I I.tangent ∞ (T% Y) ↔
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun q : U ↦ Y q) := by
    constructor
    · intro hY q
      -- Replace the pointwise bundle trivialization by the global product chart on the open
      -- subset, which identifies the section coordinate map with `Y` itself.
      have hYq : ContMDiffAt I I.tangent ∞ (T% Y) q := hY q
      rw [Bundle.contMDiffAt_section q] at hYq
      have hEq :
          (fun r : U ↦
            (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) q ⟨r, Y r⟩).2) =
            fun r : U ↦ Y r := by
        funext r
        have htoProd :=
          tangent_bundle_opens_trivializationAt_eq_toProd (I := I) (U := U) q
        simpa [Bundle.TotalSpace.toProd] using
          congrArg Prod.snd (congrArg (fun f => f ⟨r, Y r⟩) htoProd)
      simpa [hEq] using hYq
    · intro hY q
      -- The same global trivialization turns smooth Euclidean coordinates back into a smooth
      -- tangent-bundle section.
      have hYq : ContMDiffAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun r : U ↦ Y r) q := hY q
      have hEq :
          (fun r : U ↦
            (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) q ⟨r, Y r⟩).2) =
            fun r : U ↦ Y r := by
        funext r
        have htoProd :=
          tangent_bundle_opens_trivializationAt_eq_toProd (I := I) (U := U) q
        simpa [Bundle.TotalSpace.toProd] using
          congrArg Prod.snd (congrArg (fun f => f ⟨r, Y r⟩) htoProd)
      rw [Bundle.contMDiffAt_section q]
      simpa [hEq] using hYq
  have hcoord :
      (fun q : U ↦ NormedSpace.fromTangentSpace (I q)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : U ↦ I r) q (Y q))) =
        fun q : U ↦ Y q := by
    funext q
    -- On the target open subset, the explicit coordinate formula collapses to the same tangent
    -- vector because the open-subset chart is global.
    exact openSubsetCoordinate_eq_self (I := I) U q (Y q)
  rw [hcoord]
  exact hraw

/-- Helper for Proposition 8.1: the chart-target coordinate map of the transported field agrees
with the theorem's explicit source-side chart coordinate formula. -/
private lemma chartPullbackCoordinate_comp_eq_inChart
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    (X : ∀ p : M, TangentSpace I p) :
    let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
    let V : TopologicalSpace.Opens H := ⟨e.target, e.open_target⟩
    let XU : ∀ p : U, TangentSpace I p :=
      VectorField.mpullback I I (Subtype.val : U → M) X
    let F : U ≃ₘ⟮I, I⟯ V := chartSourceTargetDiffeomorph (I := I) e he
    let Y : ∀ q : V, TangentSpace I q := VectorField.mpullback I I F.symm XU
    let inChart : M → EuclideanSpace ℝ (Fin n) := fun p ↦
      NormedSpace.fromTangentSpace (e.extend I p)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p (X p))
    (fun p : U ↦
      NormedSpace.fromTangentSpace (I (F p))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p) (Y (F p)))) =
      fun p : U ↦ inChart p.1 := by
  let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
  let V : TopologicalSpace.Opens H := ⟨e.target, e.open_target⟩
  let XU : ∀ p : U, TangentSpace I p :=
    VectorField.mpullback I I (Subtype.val : U → M) X
  let F : U ≃ₘ⟮I, I⟯ V := chartSourceTargetDiffeomorph (I := I) e he
  let Y : ∀ q : V, TangentSpace I q := VectorField.mpullback I I F.symm XU
  let inChart : M → EuclideanSpace ℝ (Fin n) := fun p ↦
    NormedSpace.fromTangentSpace (e.extend I p)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p (X p))
  funext p
  have hcoordFun :
      ((fun r : V ↦ I r) ∘ F) = (e.extend I) ∘ (Subtype.val : U → M) := by
    funext q
    -- The chart diffeomorphism is the source-target homeomorphism of `e`, so composing it with
    -- the target open-subset coordinates is exactly the extended chart on the source.
    change I (F q) = I (e q)
    have hFapply : F q = e.toHomeomorphSourceTarget q := by
      simpa [F] using chartSourceTargetDiffeomorph_apply (I := I) e he q
    simpa using congrArg (fun z : V ↦ I z) hFapply
  have hcoordAt :
      MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p) := by
    -- On the target open subset, the preferred chart is the explicit coordinate map `r ↦ I r`.
    simpa [extChartAt_coe, TopologicalSpace.Opens.chartAt_eq, chartAt_self_eq] using
      (contMDiffAt_extChartAt (I := I) (n := (∞ : ℕ∞ω)) (x := F p)).mdifferentiableAt (by simp)
  have hFAt : MDifferentiableAt I I F p := F.contMDiff.mdifferentiableAt (by simp)
  have hsubAt : MDifferentiableAt I I (Subtype.val : U → M) p := by
    exact
      (contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)).mdifferentiableAt
        (by simp)
  have hextAt :
      MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p.1 :=
    mdifferentiableAt_extend (I := I) e he p.2
  have hpush :
      Y (F p) = mfderiv I I F p (XU p) := by
    -- Pulling back by `F.symm` and then evaluating at `F p` pushes the vector forward by `F`.
    simpa [Y, F] using mpullback_diffeomorph_symm_apply (I := I) (J := I) F XU p
  have hchainLeft :
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p)
          (mfderiv I I F p (XU p)) =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (((fun r : V ↦ I r) ∘ F)) p (XU p) := by
    -- Differentiate the left-hand composite in the chart-target coordinates.
    symm
    simpa [Function.comp] using
      (mfderiv_comp_apply (x := p)
        (g := fun r : V ↦ I r) (f := F) hcoordAt hFAt (XU p))
  have hchainRight :
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (((e.extend I) ∘ (Subtype.val : U → M))) p
          (XU p) =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p.1
          (mfderiv I I (Subtype.val : U → M) p (XU p)) := by
    -- Differentiating the source-side factorization introduces the derivative of the open
    -- inclusion `Subtype.val`.
    simpa [Function.comp] using
      (mfderiv_comp_apply_of_eq (x := p)
        (g := e.extend I) (f := (Subtype.val : U → M))
        hextAt hsubAt rfl (XU p))
  have hcoordDeriv :
      mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p)
          (mfderiv I I F p (XU p)) =
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p.1
          (mfderiv I I (Subtype.val : U → M) p (XU p)) := by
    have hcompMfderiv :
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (((fun r : V ↦ I r) ∘ F)) p =
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (((e.extend I) ∘ (Subtype.val : U → M))) p := by
      exact mfderiv_congr (x := p) hcoordFun
    have hmid :
        mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (((fun r : V ↦ I r) ∘ F)) p (XU p) =
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (((e.extend I) ∘ (Subtype.val : U → M))) p
            (XU p) := by
      simpa using congrArg
        (fun L : TangentSpace I p →L[ℝ] EuclideanSpace ℝ (Fin n) ↦ L (XU p)) hcompMfderiv
    -- Rewrite the differentiated target composite through the explicit function equality.
    exact hchainLeft.trans (hmid.trans hchainRight)
  have hsubApply :
      mfderiv I I (Subtype.val : U → M) p (XU p) = X p.1 := by
    -- The restricted field `XU` was defined by pulling `X` back along the open inclusion.
    simpa [tangentMap] using tangentMap_subtype_val_pullback_eq (I := I) U X p
  have hbase :
      I (F p) = e.extend I p.1 := by
    -- Evaluating the function identity at `p` aligns the target chart point with the source chart
    -- point used in `inChart`.
    simpa [Function.comp] using congrArg (fun f : U → EuclideanSpace ℝ (Fin n) ↦ f p) hcoordFun
  have hpoint :
      NormedSpace.fromTangentSpace (I (F p))
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p) (Y (F p))) =
      inChart p.1 := by
    -- Replace the transported target-open coordinate by the differentiated source chart formula.
    calc
      NormedSpace.fromTangentSpace (I (F p))
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p) (Y (F p)))
          =
        NormedSpace.fromTangentSpace (I (F p))
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) (F p)
            (mfderiv I I F p (XU p))) := by
              rw [hpush]
      _ =
        NormedSpace.fromTangentSpace (e.extend I p.1)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p.1
            (mfderiv I I (Subtype.val : U → M) p (XU p))) := by
              rw [hbase]
              exact congrArg (NormedSpace.fromTangentSpace (e.extend I p.1)) hcoordDeriv
      _ =
        NormedSpace.fromTangentSpace (e.extend I p.1)
          (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p.1 (X p.1)) := by
              rw [hsubApply]
      _ = inChart p.1 := rfl
  simpa [Y, F, inChart] using hpoint

/-- Proposition 8.1 (Smoothness Criterion for Vector Fields): the smoothness of a rough vector
field on a chart source is equivalent to the smoothness of its Euclidean-valued chart-coordinate
representation. This is the source-facing bridge from the canonical tangent-bundle section
criterion to the usual chart-coordinate vector field. -/
theorem smooth_on_chart_iff_smooth_in_chart
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    (X : ∀ p : M, TangentSpace I p) :
    let inChart : M → EuclideanSpace ℝ (Fin n) := fun p ↦
      NormedSpace.fromTangentSpace (e.extend I p)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p (X p))
    ContMDiffOn I I.tangent ∞ (T% X) e.source ↔
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ inChart e.source := by
  let U : TopologicalSpace.Opens M := ⟨e.source, e.open_source⟩
  let V : TopologicalSpace.Opens H := ⟨e.target, e.open_target⟩
  let XU : ∀ p : U, TangentSpace I p :=
    VectorField.mpullback I I (Subtype.val : U → M) X
  let F : U ≃ₘ⟮I, I⟯ V := chartSourceTargetDiffeomorph (I := I) e he
  let Y : ∀ q : V, TangentSpace I q := VectorField.mpullback I I F.symm XU
  let inChart : M → EuclideanSpace ℝ (Fin n) := fun p ↦
    NormedSpace.fromTangentSpace (e.extend I p)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p (X p))
  -- Route correction: the raw-set `extend`/`mpullbackWithin` route was replaced by two structural
  -- steps that are now verified: first restrict to the source open subtype, then transport by the
  -- chart diffeomorphism `F : U ≃ₘ⟮I, I⟯ V`.
  have hsource :
      ContMDiffOn I I.tangent ∞ (T% X) e.source ↔
        ContMDiff I I.tangent ∞ (T% XU) :=
    smoothOnSource_iff_smoothRestrictedVectorField (I := I) e X
  have htransport :
      ContMDiff I I.tangent ∞ (T% XU) ↔
        ContMDiff I I.tangent ∞ (T% Y) :=
    smoothRestrictedVectorField_iff_smoothChartPullback (I := I) e he X
  let coordY : V → EuclideanSpace ℝ (Fin n) := fun q ↦
    NormedSpace.fromTangentSpace (I q)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (fun r : V ↦ I r) q (Y q))
  have hcoordY :
      ContMDiff I I.tangent ∞ (T% Y) ↔
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ coordY :=
    smoothOpenSubsetVectorField_iff_smoothCoordinates (I := I) V Y
  have hrestrict :
      ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ inChart e.source ↔
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : U ↦ inChart p.1) :=
    contMDiffOn_iff_contMDiff_restrict
      (I := I) (J := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) U inChart
  have hbridge :
      (fun p : U ↦ coordY (F p)) = fun p : U ↦ inChart p.1 := by
    simpa [coordY] using chartPullbackCoordinate_comp_eq_inChart (I := I) e he X
  have hbridgeSymm :
      coordY = (fun p : U ↦ inChart p.1) ∘ F.symm := by
    funext q
    -- Evaluate the forward bridge at `F.symm q` to recover the target-open coordinate map.
    have hEval := congrArg (fun f : U → EuclideanSpace ℝ (Fin n) ↦ f (F.symm q)) hbridge
    simpa [Function.comp] using hEval
  constructor
  · intro hX
    -- Follow the verified route: restrict to the source subtype, transport through the chart
    -- diffeomorphism, convert to target-open coordinates, and then rewrite back to `inChart`.
    have hXU : ContMDiff I I.tangent ∞ (T% XU) := hsource.mp hX
    have hY : ContMDiff I I.tangent ∞ (T% Y) := htransport.mp hXU
    have hcoord : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ coordY := hcoordY.mp hY
    have hcomp :
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : U ↦ coordY (F p)) :=
      hcoord.comp F.contMDiff
    have hsourceCoord :
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : U ↦ inChart p.1) := by
      simpa [hbridge] using hcomp
    exact hrestrict.mpr hsourceCoord
  · intro hChart
    -- Reverse the same route: read the source restriction as a smooth map on `U`, pull it to the
    -- chart target through `F.symm`, then convert the target-open coordinates back to a section.
    have hsourceCoord :
        ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (fun p : U ↦ inChart p.1) :=
      hrestrict.mp hChart
    have hcoord : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ coordY := by
      have hcomp :
          ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
            ((fun p : U ↦ inChart p.1) ∘ F.symm) :=
        hsourceCoord.comp F.symm.contMDiff
      simpa [Function.comp, hbridgeSymm] using hcomp
    have hY : ContMDiff I I.tangent ∞ (T% Y) := hcoordY.mpr hcoord
    have hXU : ContMDiff I I.tangent ∞ (T% XU) := htransport.mpr hY
    exact hsource.mpr hXU

omit [IsManifold I (∞ : ℕ∞ω) M] in
/-- Helper for Proposition 8.1: a Euclidean-valued map is smooth on a chart source exactly when
all of its scalar coordinate functions are smooth there. -/
theorem smoothEuclideanMap_iff_smoothComponents
    (e : OpenPartialHomeomorph M H)
    (v : M → EuclideanSpace ℝ (Fin n)) :
    ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ v e.source ↔
      ∀ i : Fin n, ContMDiffOn I 𝓘(ℝ) ∞ (fun p ↦ (v p).ofLp i) e.source := by
  constructor
  · intro hv i
    -- Postcompose with `WithLp.ofLp` to pass from Euclidean-space smoothness to smoothness of the
    -- coordinate tuple, then project to the requested component.
    have hofLp : ContDiff ℝ ∞ (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) :=
      PiLp.contDiff_ofLp
    have hcomp := hofLp.contMDiff.comp_contMDiffOn hv
    simpa using (contMDiffOn_pi_space.mp hcomp) i
  · intro hv
    -- First assemble the scalar coordinate smoothness into smoothness of the tuple-valued map,
    -- then postcompose with `WithLp.toLp 2` to recover the Euclidean-space map.
    have hpi : ContMDiffOn I 𝓘(ℝ, Fin n → ℝ) ∞ (fun p ↦ (v p).ofLp) e.source := by
      exact contMDiffOn_pi_space.mpr hv
    have htoLp : ContDiff ℝ ∞ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
      PiLp.contDiff_toLp
    have hcomp := htoLp.contMDiff.comp_contMDiffOn hpi
    simpa using hcomp

/-- Helper for Proposition 8.1: the Euclidean-valued chart criterion is equivalent to smoothness
of the individual scalar chart components. -/
theorem smooth_on_chart_iff_smooth_components
    (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I (∞ : ℕ∞ω) M)
    (X : ∀ p : M, TangentSpace I p) :
    let inChart : M → Fin n → ℝ := fun p ↦
      (NormedSpace.fromTangentSpace (e.extend I p)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (e.extend I) p (X p))).ofLp
    ContMDiffOn I I.tangent ∞ (T% X) e.source ↔
      ∀ i : Fin n, ContMDiffOn I 𝓘(ℝ) ∞ (fun p ↦ inChart p i) e.source := by
  -- Unfold the chart-component tuple so the first theorem and the Euclidean helper apply
  -- directly to the same coordinate representation.
  dsimp
  -- First rewrite section smoothness as smoothness of the Euclidean chart representative, then
  -- reduce that Euclidean smoothness to scalar componentwise smoothness.
  exact (smooth_on_chart_iff_smooth_in_chart (I := I) e he X).trans
    (smoothEuclideanMap_iff_smoothComponents (I := I) e _)

end
