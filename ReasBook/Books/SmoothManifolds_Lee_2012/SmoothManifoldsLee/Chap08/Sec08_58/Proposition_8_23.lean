import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_32.Definition_5_32_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Definition_5_36_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_36.Proposition_5_49
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_58.Definition_8_58_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

-- Domain sampling pass:
-- * source-facing layer: restriction of an ambient smooth vector field to an immersed submanifold;
-- * core/canonical smooth-field owner: bundled smooth tangent sections
--   `Cₛ^∞⟮I; E, TangentSpace I⟯`;
-- * source-facing immersed-submanifold owner: the Chapter 5 predicate
--   `IsImmersedSubmanifold I J S`;
-- * source-facing tangency owner: the intrinsic Chapter 8 predicate
--   `VectorField.IsTangentToSubmanifold`, defined pointwise by membership in `T[J; p]`;
-- * bridge/view layer: the relation to the inclusion `S ↪ M` is the chapter predicate
--   `VectorField.f_related`.
-- Primitive data for tangency is still the underlying rough section, but smooth vector fields
-- should use the chapter's bundled owner rather than a raw section plus a separate smoothness
-- conjunct in the public statement.

section

universe u𝕜 uE uH uM uE' uH'

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners 𝕜 E' H'} {S : Set M}
variable [ChartedSpace H' S] [IsManifold J ∞ S]

namespace VectorField

local notation "SmoothVectorFieldOnM" => Cₛ^∞⟮I; E, TangentSpace I⟯
local notation "SmoothVectorFieldOnS" => Cₛ^∞⟮J; E', TangentSpace J⟯

/-- Helper for Proposition 8.23: on an open set, ambient smoothness is equivalent to smoothness of
the restricted map on the corresponding open subtype. -/
private lemma contMDiffOn_iff_contMDiff_restrict
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {H'' : Type*} [TopologicalSpace H'']
    {K : ModelWithCorners 𝕜 F H''}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H'' N]
    [IsManifold K (∞ : ℕ∞ω) N]
    (U : TopologicalSpace.Opens S) (f : S → N) :
    ContMDiffOn J K ∞ f U ↔ ContMDiff J K ∞ (fun x : U ↦ f x) := by
  constructor
  · intro hf x
    -- Upgrade smoothness on the open set to ambient smoothness at `x`, then reinterpret it on the
    -- corresponding open subtype.
    have hxWithin : ContMDiffWithinAt J K ∞ f (U : Set S) x := hf x x.2
    have hxAt : ContMDiffAt J K ∞ f x := hxWithin.contMDiffAt (U.2.mem_nhds x.2)
    exact (contMDiffAt_subtype_iff (U := U) (f := f) (x := x)).2 hxAt
  · intro hf x hx
    -- Conversely, read the restricted smoothness at `⟨x, hx⟩` as ambient smoothness at `x`.
    let xU : U := ⟨x, hx⟩
    have hxAt : ContMDiffAt J K ∞ f x := by
      exact (contMDiffAt_subtype_iff (U := U) (f := f) (x := xU)).1 (hf xU)
    exact hxAt.contMDiffWithinAt

/-- Helper for Proposition 8.23: the derivative of a `C^∞` diffeomorphism is invertible at every
point. -/
private lemma diffeomorph_mfderiv_isInvertible
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
    [IsManifold J (∞ : ℕ∞ω) M']
    (F : S ≃ₘ⟮J, J⟯ M') (x : S) :
    (mfderiv J J F x).IsInvertible := by
  -- Package the derivative as the canonical linear equivalence supplied by the diffeomorphism API.
  let e := F.mfderivToContinuousLinearEquiv (by simp) x
  refine ⟨e, ?_⟩
  simpa [e] using
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := F) (hn := by simp) (x := x)).symm

/-- Helper for Proposition 8.23: a maximal-atlas chart is a diffeomorphism between its source open
subtype and its target open subtype. -/
private def chartSourceTargetDiffeomorph
    (e : OpenPartialHomeomorph S H')
    (he : e ∈ IsManifold.maximalAtlas J (∞ : ℕ∞ω) S) :
    (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) ≃ₘ⟮J, J⟯
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') where
  toEquiv := e.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    intro x
    let f :
        (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) →
          (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') := fun x ↦
      show (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') from
        e.toHomeomorphSourceTarget x
    -- Coerce away the target subtype so the goal matches the ambient chart map.
    refine (ContMDiffAt.subtypeVal_comp_iff
      (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') f x).1 ?_
    refine (contMDiffAt_subtype_iff
      (U := (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S))
      (f := fun x : S ↦ e x) (x := x)).2 ?_
    simpa using
      (contMDiffAt_of_mem_maximalAtlas
        (I := J) (n := (∞ : ℕ∞ω)) (e := e) he x.2)
  contMDiff_invFun := by
    intro y
    let f :
        (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H') →
          (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) := fun y ↦
      show (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) from
        e.toHomeomorphSourceTarget.symm y
    -- Coerce away the source subtype so the goal matches the ambient inverse chart map.
    refine (ContMDiffAt.subtypeVal_comp_iff
      (⟨e.source, e.open_source⟩ : TopologicalSpace.Opens S) f y).1 ?_
    refine (contMDiffAt_subtype_iff
      (U := (⟨e.target, e.open_target⟩ : TopologicalSpace.Opens H'))
      (f := fun y : H' ↦ e.symm y) (x := y)).2 ?_
    simpa using
      (contMDiffAt_symm_of_mem_maximalAtlas
        (I := J) (n := (∞ : ℕ∞ω)) (e := e) he y.2)

/-- Helper for Proposition 8.23: lowering the differentiability index preserves immersions because
the same local normal-form charts still witness the immersion statement. -/
private theorem isImmersionOfLe
    {n m : WithTop ℕ∞} {f : S → M} (hmn : m ≤ n)
    (hf : Manifold.IsImmersion J I n f) :
    Manifold.IsImmersion J I m f := by
  -- Keep the same complement choice and the same pointwise chart presentation.
  let hComp := hf.complement
  let hCompImm := hf.isImmersionOfComplement_complement
  refine ⟨hComp, inferInstance, inferInstance, ?_⟩
  intro x
  let hx := hCompImm x
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts
    hx.equiv hx.domChart hx.codChart hx.mem_domChart_source hx.mem_codChart_source ?_ ?_
    hx.source_subset_preimage_source hx.writtenInCharts
  · exact (IsManifold.maximalAtlas_subset_of_le (I := J) (M := S) hmn) hx.domChart_mem_maximalAtlas
  · exact (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M) hmn) hx.codChart_mem_maximalAtlas

/-- Helper for Proposition 8.23: choose, at each `p : S`, the unique intrinsic tangent vector
whose image under the derivative of the inclusion equals the ambient tangent vector `Y p`
guaranteed by tangency. -/
private noncomputable def restrictionChoice
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) :
    ∀ p : S, TangentSpace J p :=
  fun p ↦
    Classical.choose <|
      (isTangentToSubmanifoldAt_iff_exists (J := J) (X := Y) p).mp (hYtangent p)

/-- Helper for Proposition 8.23: the chosen intrinsic tangent vector at `p : S` maps to the given
ambient tangent vector `Y p` under the derivative of the subtype inclusion. -/
private theorem restrictionChoice_spec
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) (p : S) :
    mfderiv J I (Subtype.val : S → M) p (restrictionChoice (J := J) Y hYtangent p) = Y p := by
  -- Unpack the witness used to define the pointwise restriction candidate.
  exact
    Classical.choose_spec <|
      (isTangentToSubmanifoldAt_iff_exists (J := J) (X := Y) p).mp (hYtangent p)

/-- Helper for Proposition 8.23: the pointwise chosen field is already related to `Y`; only its
smoothness remains to be proved locally. -/
private theorem restrictionChoice_f_related
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) :
    f_related (Subtype.val : S → M) (restrictionChoice (J := J) Y hYtangent) Y := by
  -- The inclusion `Subtype.val : S → M` is smooth, and the pointwise equality is the defining
  -- property of the chosen tangent vectors.
  have hsub : ContMDiff J I ∞ (Subtype.val : S → M) := by
    -- The immersed-submanifold hypothesis is exactly an immersion hypothesis on `Subtype.val`.
    let hSInf : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) :=
      isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
        (n := (⊤ : ℕ∞ω)) (by simp) hS
    simpa using hSInf.contMDiff
  refine ⟨hsub, ?_⟩
  intro p
  exact restrictionChoice_spec (J := J) Y hYtangent p

/-- Helper for Proposition 8.23: every point of the immersed submanifold has an open neighborhood
whose inclusion into the ambient manifold is a smooth embedding at the current `C^∞` surface. -/
private theorem embeddedNeighborhoodAtOfImmersedSubmanifold
    (hS : IsImmersedSubmanifold I J S) (p : S) :
    ∃ U : TopologicalSpace.Opens S, p ∈ U ∧
      Manifold.IsSmoothEmbedding J I ∞ ((↑) : U → M) := by
  -- Reuse Proposition 5.49 on the top differentiability surface, then lower it to `∞`.
  letI : IsManifold I (⊤ : WithTop ℕ∞) M :=
    IsManifold.of_le (m := (⊤ : WithTop ℕ∞)) (n := (∞ : ℕ∞ω)) (by simp)
  letI : IsManifold J (⊤ : WithTop ℕ∞) S :=
    IsManifold.of_le (m := (⊤ : WithTop ℕ∞)) (n := (∞ : ℕ∞ω)) (by simp)
  obtain ⟨U, hpU, hUembTop⟩ :=
    immersed_submanifold_has_embedded_neighborhood (I := I) (I' := J) hS p
  exact ⟨U, hpU, isSmoothEmbedding_to_infty hUembTop⟩

/-- Helper for Proposition 8.23: on an embedded patch, the pointwise chosen intrinsic tangent
vector still maps to the ambient vector `Y q`. -/
private theorem restrictionChoiceOnEmbeddedPatch_spec
    {U : TopologicalSpace.Opens S}
    (Y : SmoothVectorFieldOnM) (hYtangent : IsTangentToSubmanifold S J Y) :
    ∀ q : U,
      mfderiv J I (Subtype.val : S → M) q.1
        (restrictionChoice (J := J) Y hYtangent q.1) = Y q := by
  -- This is the original pointwise defining identity, now specialized to a patch point `q : U`.
  intro q
  exact restrictionChoice_spec (J := J) Y hYtangent q.1

/-- Helper for Proposition 8.23: differentiating the immersion normal form identifies the
subtype-inclusion derivative with the chart-level model map on tangent vectors. -/
private theorem chartExtend_symm_mdifferentiableWithin_range
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N) {p : N} (hp : p ∈ e.source) :
    MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p) := by
  letI : IsManifold J 1 N :=
    IsManifold.of_le (m := 1) (n := (∞ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 N :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := N)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) he
  have hid :
      MDifferentiableWithinAt J J (id : N → N) Set.univ p := by
    -- The inverse-chart derivative bridge starts from the trivial differentiability of `id`.
    simpa using
      (mdifferentiableWithinAt_id (I := J) (s := Set.univ) (x := p) :
        MDifferentiableWithinAt J J (id : N → N) Set.univ p)
  -- Re-express `id` in chart coordinates to read off differentiability of the inverse chart.
  simpa [Function.comp] using
    (mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas
      (I := J) (I' := J) (e := e) (f := id) (s := Set.univ) he_one hp).mp hid

/-- Helper for Proposition 8.23: differentiating the chart left-inverse identity on `e.source`
produces a concrete left inverse for the derivative of `e.extend`. -/
private theorem chartExtend_mfderiv_left_inverse
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N) {p : N} (hp : p ∈ e.source) :
    (mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)).comp
      (mfderiv J 𝓘(𝕜, E') (e.extend J) p) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J p) := by
  letI : IsManifold J 1 N :=
    IsManifold.of_le (m := 1) (n := (∞ : ℕ∞ω)) (by simp)
  have he_one : e ∈ IsManifold.maximalAtlas J 1 N :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := N)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) he
  have hsource_unique : UniqueMDiffWithinAt J e.source p :=
    e.open_source.uniqueMDiffWithinAt hp
  have hchart :
      MDifferentiableAt J 𝓘(𝕜, E') (e.extend J) p := by
    -- Maximal-atlas charts are differentiable at every source point.
    exact
      (contMDiffAt_extend (I := J) (e := e) he_one hp).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hrange :
      MDifferentiableWithinAt 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p) :=
    chartExtend_symm_mdifferentiableWithin_range (J := J) he hp
  have hchart_within :
      mfderiv J 𝓘(𝕜, E') (e.extend J) p =
        mfderivWithin J 𝓘(𝕜, E') (e.extend J) e.source p := by
    -- On the open chart source, the within derivative agrees with the ordinary derivative.
    symm
    exact mfderivWithin_eq_mfderiv hsource_unique hchart
  rw [hchart_within, ← mfderivWithin_comp_of_eq]
  · -- Differentiate the left-inverse identity on the chart source where the source-side
    -- `UniqueMDiffWithinAt` hypothesis is available.
    rw [← mfderivWithin_id hsource_unique]
    apply Filter.EventuallyEq.mfderivWithin_eq_of_mem
    · refine Filter.eventuallyEq_of_mem self_mem_nhdsWithin ?_
      intro z hz
      simpa [Function.comp] using e.extend_left_inv (I := J) hz
    · exact hp
  · exact hrange
  · exact hchart.mdifferentiableWithinAt
  · intro z hz
    have hz_target : e.extend J z ∈ (e.extend J).target :=
      (e.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hz
    exact e.extend_target_subset_range hz_target
  · exact hsource_unique
  · rfl

/-- Helper for Proposition 8.23: the derivative of a maximal-atlas chart is injective because
the chart inverse cancels it on the chart source. -/
private theorem chartExtend_mfderiv_injective
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    {e : OpenPartialHomeomorph N H'}
    (he : e ∈ IsManifold.maximalAtlas J ∞ N) {p : N} (hp : p ∈ e.source) :
    Function.Injective (mfderiv J 𝓘(𝕜, E') (e.extend J) p) := by
  let Linv :=
    mfderivWithin 𝓘(𝕜, E') J (e.extend J).symm (Set.range J) (e.extend J p)
  intro w₁ w₂ hw
  have hleft := chartExtend_mfderiv_left_inverse (J := J) he hp
  have hp_left : (e.extend J).symm (e.extend J p) = p :=
    e.extend_left_inv (I := J) hp
  have hw_push : Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₁) =
      Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₂) := by
    simpa [Linv] using congrArg Linv hw
  have hw₁ :
      ((Linv.comp (mfderiv J 𝓘(𝕜, E') (e.extend J) p)) w₁) = w₁ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₁) hleft
  have hw₂ :
      ((Linv.comp (mfderiv J 𝓘(𝕜, E') (e.extend J) p)) w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using congrArg (fun L ↦ L w₂) hleft
  have hw₁' : w₁ = Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₁) := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₁.symm
  have hw₂' : Linv (mfderiv J 𝓘(𝕜, E') (e.extend J) p w₂) = w₂ := by
    simpa [Linv, hp_left, ContinuousLinearMap.comp_apply] using hw₂
  -- Apply the derivative-level left inverse to both chart-coordinate tangent vectors.
  exact hw₁'.trans (hw_push.trans hw₂')

/-- Helper for Proposition 8.23: differentiating the immersion normal form identifies the
subtype-inclusion derivative with the chart-level model map on tangent vectors. -/
private theorem subtypeVal_chartPushforward_eq_model
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S) (w : TangentSpace J p) :
    let hImmAt := hImm.isImmersionAt p
    let L : E' →L[𝕜] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
    (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
      (mfderiv J I (Subtype.val : S → M) p w) =
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hdomChart_source : hImmAt.domChart.source ∈ nhds p :=
    IsOpen.mem_nhds hImmAt.domChart.open_source hImmAt.mem_domChart_source
  have hEqOn :
      Set.EqOn ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))
        (L ∘ (hImmAt.domChart.extend J)) hImmAt.domChart.source := by
    intro y hy
    -- Read the immersion normal form directly on the source chart neighborhood.
    have hy_target :
        hImmAt.domChart.extend J y ∈ (hImmAt.domChart.extend J).target :=
      (hImmAt.domChart.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hy
    simpa [Function.comp, L, OpenPartialHomeomorph.extend_coe,
      hImmAt.domChart.left_inv hy, ContinuousLinearMap.comp_apply] using
      hImmAt.writtenInCharts hy_target
  have hEq :
      ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M)) =ᶠ[nhds p]
        L ∘ (hImmAt.domChart.extend J) :=
    hEqOn.eventuallyEq_of_mem hdomChart_source
  have hsub :
      MDifferentiableAt J I (Subtype.val : S → M) p :=
    hImm.contMDiff.mdifferentiableAt (by simp : (∞ : ℕ∞ω) ≠ 0)
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hcodChart_mem_maximalAtlas_one :
      hImmAt.codChart ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.codChart_mem_maximalAtlas
  have hdom :
      MDifferentiableAt J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p := by
    -- Maximal-atlas charts are differentiable in model coordinates.
    exact
      (contMDiffAt_extend (I := J) (e := hImmAt.domChart)
        hdomChart_mem_maximalAtlas_one hImmAt.mem_domChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hcod :
      MDifferentiableAt I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p) := by
    -- The ambient chart enjoys the same differentiability property.
    exact
      (contMDiffAt_extend (I := I) (e := hImmAt.codChart)
        hcodChart_mem_maximalAtlas_one hImmAt.mem_codChart_source).mdifferentiableAt
        (by simp : (1 : ℕ∞ω) ≠ 0)
  have hL :
      MDifferentiableAt 𝓘(𝕜, E') 𝓘(𝕜, E) L (hImmAt.domChart.extend J p) := by
    -- The linear model map differentiates to itself.
    exact L.contMDiffAt.mdifferentiableAt (by simp : (1 : ℕ∞ω) ≠ 0)
  have hmfderiv_eq :
      mfderiv J 𝓘(𝕜, E) (((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))) p =
        mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p := by
    -- Differentiate the two eventually equal source-side expressions at the base point.
    exact hEq.mfderiv_eq
  have hleft :
      (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
        (mfderiv J I (Subtype.val : S → M) p w) =
      mfderiv J 𝓘(𝕜, E) (((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M))) p w := by
    symm
    exact mfderiv_comp_apply (x := p) hcod hsub w
  have hright :
      mfderiv J 𝓘(𝕜, E) (L ∘ (hImmAt.domChart.extend J)) p w =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w) := by
    simpa [Function.comp, mfderiv_eq_fderiv] using
      (mfderiv_comp_apply (x := p) (g := L) (f := hImmAt.domChart.extend J)
        hL hdom w)
  -- Apply the chain rule on both sides of the source-side equality.
  exact hleft.trans <| hmfderiv_eq ▸ hright

/-- Helper for Proposition 8.23: the manifold derivative of an immersed subtype inclusion is
injective at every point. -/
private theorem subtypeVal_mfderiv_injective
    (hImm : Manifold.IsImmersion J I ∞ (Subtype.val : S → M))
    (p : S) :
    Function.Injective (mfderiv J I (Subtype.val : S → M) p) := by
  let hImmAt := hImm.isImmersionAt p
  let L : E' →L[𝕜] E :=
    hImmAt.equiv.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl 𝕜 E' hImmAt.complement)
  have hL_injective : Function.Injective L := by
    intro u v huv
    have hpair :
        (u, (0 : hImmAt.complement)) = (v, (0 : hImmAt.complement)) := by
      apply hImmAt.equiv.injective
      simpa [L, ContinuousLinearMap.comp_apply] using huv
    exact (Prod.mk.inj hpair).1
  intro w₁ w₂ hw
  have hw_chart :
      L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁) =
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
    have hw₁_model :
        L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁) =
          (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
            (mfderiv J I (Subtype.val : S → M) p w₁) := by
      simpa [hImmAt, L] using
        (subtypeVal_chartPushforward_eq_model (I := I) (J := J) hImm p w₁).symm
    have hw₂_model :
        (mfderiv I 𝓘(𝕜, E) (hImmAt.codChart.extend I) ((Subtype.val : S → M) p))
            (mfderiv J I (Subtype.val : S → M) p w₂) =
          L ((mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂) := by
      simpa [hImmAt, L] using subtypeVal_chartPushforward_eq_model (I := I) (J := J) hImm p w₂
    -- Compare the two vectors after applying the ambient chart derivative.
    exact hw₁_model.trans <| by simpa [hw] using hw₂_model
  have hdomChart_mem_maximalAtlas_one :
      hImmAt.domChart ∈ IsManifold.maximalAtlas J 1 S :=
    IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
      (m := 1) (n := (∞ : ℕ∞ω)) (by simp) hImmAt.domChart_mem_maximalAtlas
  have hsource_chart :
      (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₁ =
        (mfderiv J 𝓘(𝕜, E') (hImmAt.domChart.extend J) p) w₂ :=
    hL_injective hw_chart
  exact
    chartExtend_mfderiv_injective (J := J) hImmAt.domChart_mem_maximalAtlas
      hImmAt.mem_domChart_source hsource_chart

/-- Helper for Proposition 8.23: the pointwise chosen intrinsic restriction field is smooth at a
fixed point once one transports the problem to an embedded neighborhood patch. -/
private theorem restrictionChoiceContMDiffAt
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y) (p : S) :
    ContMDiffAt J J.tangent ∞ (T% (restrictionChoice (J := J) Y hYtangent)) p := by
  -- Route correction: first isolate an embedded neighborhood on the current `∞` surface, so the
  -- remaining work is only the chart-to-tangent-bundle coordinate transport on that patch.
  obtain ⟨U, hpU, hUemb⟩ :=
    embeddedNeighborhoodAtOfImmersedSubmanifold (I := I) (J := J) hS p
  let q0 : U := ⟨p, hpU⟩
  have hq0_spec :
      mfderiv J I (Subtype.val : S → M) q0.1
        (restrictionChoice (J := J) Y hYtangent q0.1) = Y q0 := by
    exact restrictionChoiceOnEmbeddedPatch_spec (J := J) Y hYtangent q0
  -- TODO: read `hXU_related` in the immersion charts from `hUemb.isImmersion.isImmersionAt q0`,
  -- convert `restrictionChoice_spec` into the projected ambient chart-coordinate formula, and then
  -- close the pointwise smoothness goal with `Bundle.contMDiffAt_section`.
  sorry

/-- Proposition 8.23: if `Y` is a smooth vector field on `M` tangent to the immersed submanifold
`S`, then there exists a unique smooth vector field on `S` that is related to `Y` by the subtype
inclusion `ι : S ↪ M`. This is the restriction `Y|_S` from the text. -/
theorem existsUnique_restriction_to_submanifold
    (hS : IsImmersedSubmanifold I J S)
    (Y : SmoothVectorFieldOnM)
    (hYtangent : IsTangentToSubmanifold S J Y) :
    ∃! X : SmoothVectorFieldOnS,
      f_related (Subtype.val : S → M) X Y := by
  let X0 : ∀ p : S, TangentSpace J p := restrictionChoice (J := J) Y hYtangent
  have hX0_related : f_related (Subtype.val : S → M) X0 Y :=
    restrictionChoice_f_related (I := I) (J := J) hS Y hYtangent
  have hX0_smooth : ContMDiff J J.tangent ∞ (T% X0) := by
    -- Smoothness is local on `S`, so it suffices to invoke the embedded-patch pointwise lemma.
    intro p
    exact restrictionChoiceContMDiffAt (I := I) (J := J) hS Y hYtangent p
  let X : SmoothVectorFieldOnS := ContMDiffSection.mk X0 hX0_smooth
  refine ⟨X, ?_, ?_⟩
  · -- Existence is immediate once the chosen pointwise field is known to be smooth.
    simpa [X, X0] using hX0_related
  · intro X' hX'
    -- Uniqueness is pointwise: the immersed inclusion has injective derivative at every point, so
    -- any related field must agree with the chosen tangent vector whose image is `Y p`.
    have hSInf : Manifold.IsImmersion J I ∞ (Subtype.val : S → M) := by
      exact
        isImmersionOfLe (I := I) (J := J) (S := S) (m := (∞ : ℕ∞ω))
          (n := (⊤ : ℕ∞ω)) (by simp) hS
    refine ContMDiffSection.ext ?_
    intro p
    -- Push both candidates through the subtype derivative and cancel the common ambient vector.
    apply subtypeVal_mfderiv_injective (I := I) (J := J) hSInf p
    exact
      (VectorField.f_related_apply hX' p).trans
        (VectorField.f_related_apply hX0_related p).symm

end VectorField

end
