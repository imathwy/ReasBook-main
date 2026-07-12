import Mathlib.Geometry.Manifold.GroupLieAlgebra
import SmoothManifolds_Lee_2012.Chap08.Sec08_57.Definition_8_57_extra_1
import SmoothManifolds_Lee_2012.Chap08.Sec08_60.Notation_8_60_extra_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff

universe u𝕜 uEG uHG uG uEH uHH uH

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG] [CompleteSpace EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH] [CompleteSpace EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EG HG} {J : ModelWithCorners 𝕜 EH HH}
variable {G : Type uG} [TopologicalSpace G] [ChartedSpace HG G] [Group G]
variable {H : Type uH} [TopologicalSpace H] [ChartedSpace HH H] [Group H]
variable [LieGroup I (minSmoothness 𝕜 3) G] [LieGroup J (minSmoothness 𝕜 3) H]

-- Domain sampling pass:
-- * primary domain: Lie-group homomorphisms acting on Lie algebras and left-invariant vector
--   fields;
-- * source-facing owner for the induced-field relation: `VectorField.f_related`;
-- * core/canonical owner for the induced Lie algebra map:
--   `ContMDiffMonoidMorphism.inducedLieAlgebraHomomorphism`;
-- * bridge/view theorems in this file:
--   `inducedLieAlgebraHomomorphism_related` and
--   `inducedLieAlgebraHomomorphism_related_apply`;
-- * relevant declarations inspected in this domain: `GroupLieAlgebra`,
--   `mulInvariantVectorField`, `VectorField.f_related`, and `VectorField.f_related_apply`.
-- Primitive data here is the induced Lie algebra homomorphism. The pointwise `mfderiv` identity is
-- derived API, while the source-facing theorem should live at the `f_related` layer.

namespace ContMDiffMonoidMorphism

/-- Helper for Definition 8.61-extra-1: transport the derivative codomain from
`TangentSpace J (F 1)` to `GroupLieAlgebra J H = TangentSpace J 1`. -/
theorem inducedLieAlgebraTargetLinearMapEq
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (GroupLieAlgebra I G →ₗ[𝕜] TangentSpace J (F 1)) =
      (GroupLieAlgebra I G →ₗ[𝕜] GroupLieAlgebra J H) := by
  -- This is the canonical transport coming from the identity preservation `F 1 = 1`.
  simpa [GroupLieAlgebra] using
    congrArg (fun h : H ↦ GroupLieAlgebra I G →ₗ[𝕜] TangentSpace J h) F.map_one

/-- Helper for Definition 8.61-extra-1: the derivative at the identity, viewed as a linear map
between the source and target Lie algebras. -/
noncomputable def inducedLieAlgebraLinearMap
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    GroupLieAlgebra I G →ₗ[𝕜] GroupLieAlgebra J H :=
  Eq.mp (inducedLieAlgebraTargetLinearMapEq F) (mfderiv I J F (1 : G)).toLinearMap

/-- Helper for Definition 8.61-extra-1: evaluating the transported derivative-at-identity map is
just the ordinary derivative at the identity, with the codomain cast collapsed. -/
theorem inducedLieAlgebraLinearMap_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    inducedLieAlgebraLinearMap F X = (mfderiv I J F (1 : G)) X := by
  -- Unfold the transported linear map and collapse the identity-fiber cast on the tangent vector.
  unfold inducedLieAlgebraLinearMap
  change
    cast (by
      simpa [GroupLieAlgebra] using congrArg (fun h : H ↦ TangentSpace J h) F.map_one)
      ((mfderiv I J F (1 : G)) X) = (mfderiv I J F (1 : G)) X
  exact eq_of_heq (cast_heq _ _)

/-- Helper for Definition 8.61-extra-1: differentiating the multiplicativity identity shows that
the pushforward of a left-invariant vector field is the left-invariant vector field determined by
the identity derivative. -/
-- TODO: Differentiate `F ∘ (g * ·) = ((F g) * ·) ∘ F` at `1`, then normalize the resulting
-- transport from `TangentSpace J (F 1)` to `TangentSpace J 1` via `F.map_one`.
theorem inducedLieAlgebraLinearMap_mulInvariantVectorField_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) (g : G) :
    mfderiv I J F g (Xᴸ g) = (inducedLieAlgebraLinearMap F X)ᴸ (F g) := by
  have hmin : minSmoothness 𝕜 3 ≠ 0 :=
    lt_of_lt_of_le (by simp) le_minSmoothness |>.ne'
  have hF : MDifferentiableAt I J F g :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hF_one : MDifferentiableAt I J F (1 : G) :=
    F.contMDiff_toFun.mdifferentiableAt (by simp)
  have hmulG : MDifferentiableAt I I (g * ·) (1 : G) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hmulH : MDifferentiableAt J J ((F g) * ·) (1 : H) :=
    contMDiff_mul_left.contMDiffAt.mdifferentiableAt hmin
  have hcomp :
      F ∘ (g * ·) = ((F g) * ·) ∘ F := by
    -- The multiplicativity of `F` identifies the two ways of translating before or after `F`.
    ext x
    simp [map_mul]
  have hsource :
      mfderiv I J F g (Xᴸ g) = mfderiv I J (F ∘ (g * ·)) (1 : G) X := by
    -- Differentiate `F ∘ (g * ·)` at the identity and rewrite the source vector field.
    simpa [mulInvariantVectorField] using
      (mfderiv_comp_apply_of_eq (1 : G) hF hmulG (mul_one g) X).symm
  have hmiddle :
      mfderiv I J (F ∘ (g * ·)) (1 : G) X =
        mfderiv I J (((F g) * ·) ∘ F) (1 : G) X := by
    -- Replace the source composite by the multiplicativity identity for `F`.
    have hmf :
        @Eq (EG →L[𝕜] EH) (mfderiv I J (F ∘ (g * ·)) (1 : G))
          (mfderiv I J (((F g) * ·) ∘ F) (1 : G)) := by
      simpa [hcomp] using mfderiv_congr hcomp
    simpa using congrArg (fun L : EG →L[𝕜] EH ↦ L X) hmf
  have htarget :
      mfderiv I J (((F g) * ·) ∘ F) (1 : G) X =
        mfderiv J J ((F g) * ·) (1 : H) ((mfderiv I J F (1 : G)) X) := by
    -- Differentiate the target composite at the identity of `G`.
    simpa using
      mfderiv_comp_apply_of_eq (1 : G) hmulH hF_one F.map_one X
  have htransport :
      mfderiv J J ((F g) * ·) (1 : H) ((mfderiv I J F (1 : G)) X) =
        (inducedLieAlgebraLinearMap F X)ᴸ (F g) := by
    -- The final step is only the collapse of the transported identity derivative.
    rw [mulInvariantVectorField, inducedLieAlgebraLinearMap_apply]
  exact hsource.trans (hmiddle.trans (htarget.trans htransport))

/-- Helper for Definition 8.61-extra-1: package the pointwise pushforward formula as an
`f_related` statement between the associated left-invariant vector fields. -/
theorem inducedLieAlgebraLinearMap_related
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    VectorField.f_related F Xᴸ ((inducedLieAlgebraLinearMap F X)ᴸ) := by
  -- The smooth map component is already part of `ContMDiffMonoidMorphism`.
  refine ⟨F.contMDiff_toFun, ?_⟩
  intro g
  -- Reuse the established pointwise derivative identity instead of rebuilding it locally.
  simpa using inducedLieAlgebraLinearMap_mulInvariantVectorField_apply F X g

/-- Helper for Definition 8.61-extra-1: once the bracket fields are known to be `F`-related, the
Lie-algebra bracket identity follows by evaluating that relation at the identity. -/
theorem inducedLieAlgebraLinearMap_map_lie_of_related
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G)
    (hBracket :
      VectorField.f_related F
        (VectorField.mlieBracket I Xᴸ Yᴸ)
        (VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ))) :
    inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
      ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
  -- Evaluate the bracket-relatedness identity at the identity element of `G`.
  have hApply := VectorField.f_related_apply hBracket (1 : G)
  -- Normalize the target basepoint before rewriting back to Lie-algebra notation.
  have hBasepoint :
      VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (F 1) =
        VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := by
    simpa using
      congrArg
        (fun z : H ↦
          VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
            ((inducedLieAlgebraLinearMap F Y)ᴸ) z)
        F.map_one
  -- Rewrite both sides from manifold brackets back to Lie-algebra brackets.
  simpa [GroupLieAlgebra.bracket_def, inducedLieAlgebraLinearMap_apply] using
    hApply.trans hBasepoint

/-- Helper for Definition 8.61-extra-1: the preferred-chart expression of `F` at the identity is
`C^∞` within the source chart target. -/
theorem inducedLieAlgebraChartMapContDiffWithinAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let G' := ψ ∘ F ∘ φ.symm
    ContDiffWithinAt 𝕜 ∞ G' φ.target (φ (1 : G)) := by
  -- Compose the source chart inverse, the smooth homomorphism `F`, and the target chart.
  dsimp
  have hComp :
      ContMDiffWithinAt 𝓘(𝕜, EG) J ∞
        (F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target
        ((extChartAt I (1 : G)) (1 : G)) := by
    exact
      (F.contMDiff_toFun.contMDiffAt (x := (1 : G))).comp_contMDiffWithinAt_of_eq
        ((contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) (1 : G)).mono
          (extChartAt_target_subset_range (I := I) (1 : G)))
        (by simp)
  have hChart :
      ContMDiffWithinAt 𝓘(𝕜, EG) 𝓘(𝕜, EH) ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target
        ((extChartAt I (1 : G)) (1 : G)) := by
    exact
      (contMDiffAt_extChartAt (I := J) (n := ∞) (x := (1 : H))).comp_contMDiffWithinAt_of_eq
        hComp (by simp)
  -- Convert the manifold statement to the chart-level `ContDiffWithinAt` statement.
  exact hChart.contDiffWithinAt

/-- Helper for Definition 8.61-extra-1: the source preferred-chart pullback of a left-invariant
vector field is differentiable within `range I` at the chart point of `1`. -/
theorem sourceMulInvariantChartPullbackDifferentiableWithinAtOne
    (Z : GroupLieAlgebra I G) :
    DifferentiableWithinAt 𝕜
      (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Zᴸ (Set.range I))
      (Set.range I) ((extChartAt I (1 : G)) (1 : G)) := by
  -- Reuse the general chart-pullback differentiability theorem for the invariant field `Zᴸ`.
  have hZAt : MDifferentiableAt I I.tangent (T% Zᴸ) (1 : G) :=
    mdifferentiableAt_mulInvariantVectorField (I := I) (G := G) (v := Z) (g := (1 : G))
  have hZ : MDifferentiableWithinAt I I.tangent (T% Zᴸ) Set.univ (1 : G) :=
    hZAt.mdifferentiableWithinAt
  simpa using hZ.differentiableWithinAt_mpullbackWithin_vectorField

/-- Helper for Definition 8.61-extra-1: the target preferred-chart pullback of a left-invariant
vector field is differentiable within `range J` at the chart point of `1`. -/
theorem targetMulInvariantChartPullbackDifferentiableWithinAtOne
    (Z : GroupLieAlgebra J H) :
    DifferentiableWithinAt 𝕜
      (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm Zᴸ (Set.range J))
      (Set.range J) ((extChartAt J (1 : H)) (1 : H)) := by
  -- Reuse the same chart-pullback differentiability theorem on the target Lie group.
  have hZAt : MDifferentiableAt J J.tangent (T% Zᴸ) (1 : H) :=
    mdifferentiableAt_mulInvariantVectorField (I := J) (G := H) (v := Z) (g := (1 : H))
  have hZ : MDifferentiableWithinAt J J.tangent (T% Zᴸ) Set.univ (1 : H) :=
    hZAt.mdifferentiableWithinAt
  simpa using hZ.differentiableWithinAt_mpullbackWithin_vectorField

/-- Helper for Definition 8.61-extra-1: near the preferred source chart of `1`, the map
`x ↦ F ((extChartAt I 1).symm x)` stays in the source of the preferred target chart at `1`. -/
theorem chartMapEventuallyIntoTargetSourceAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    (fun x : EG ↦ F ((extChartAt I (1 : G)).symm x)) ⁻¹' (extChartAt J (1 : H)).source ∈
      nhdsWithin ((extChartAt I (1 : G)) (1 : G)) (Set.range I) := by
  -- Compose continuity of `F` at `1` with continuity of the preferred source chart inverse.
  have hcont :
      ContinuousAt (fun x : EG ↦ F ((extChartAt I (1 : G)).symm x))
        ((extChartAt I (1 : G)) (1 : G)) :=
    F.contMDiff_toFun.continuous.continuousAt.comp
      (continuousAt_extChartAt_symm (I := I) (1 : G))
  exact nhdsWithin_le_nhds <|
    hcont.preimage_mem_nhds (by simpa using extChartAt_source_mem_nhds (I := J) (1 : H))

/-- Helper for Definition 8.61-extra-1: on the preferred source chart at `1`, the inverse of the
chart-inverse derivative is the ordinary derivative of the chart itself. -/
theorem sourceChartInverseDerivativeAtOne
    {x : EG} (hx : x ∈ (extChartAt I (1 : G)).target) :
    (mfderiv[Set.range I] (extChartAt I (1 : G)).symm x).inverse =
      mfderiv% (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm x) := by
  -- Normalize the source-side inverse derivative using the preferred-chart inverse identities.
  have hrightInv :
      (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm x) = x :=
    PartialEquiv.right_inv (extChartAt I (1 : G)) hx
  apply ContinuousLinearMap.inverse_eq
  · simpa [hrightInv] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
        (I := I) (x := (1 : G)) (y := x) hx
  · simpa [hrightInv] using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
        (I := I) (x := (1 : G)) (y := x) hx

/-- Helper for Definition 8.61-extra-1: on the preferred target chart at `1`, the inverse of the
chart-inverse derivative is the ordinary derivative of the chart itself. -/
theorem targetChartInverseDerivativeAtOne
    {z : H} (hz : z ∈ (extChartAt J (1 : H)).source) :
    (mfderiv[Set.range J] (extChartAt J (1 : H)).symm ((extChartAt J (1 : H)) z)).inverse =
      mfderiv% (extChartAt J (1 : H)) z := by
  -- Normalize the target-side inverse derivative with the same chart identities at `1`.
  apply ContinuousLinearMap.inverse_eq
  · simpa using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := J) (x := (1 : H)) (y := z) hz
  · simpa using
      mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm'
        (I := J) (x := (1 : H)) (y := z) hz

/-- Helper for Definition 8.61-extra-1: once the source and target chart-membership conditions
are explicit, `F`-related vector fields satisfy the preferred-chart pushforward identity
pointwise at `1`. -/
theorem chartPushforwardRelatedWithinAtOnePointwise
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {V : ∀ g : G, TangentSpace I g}
    {W : ∀ h : H, TangentSpace J h}
    (hVW : VectorField.f_related F V W) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let V' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm V (Set.range I)
    let W' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm W (Set.range J)
    ∀ ⦃x : EG⦄, x ∈ φ.target →
      F (φ.symm x) ∈ ψ.source →
      fderivWithin 𝕜 F' (Set.range I) x (V' x) = W' (F' x) := by
  let φ := extChartAt I (1 : G)
  let ψ := extChartAt J (1 : H)
  let F' := ψ ∘ F ∘ φ.symm
  let V' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm V (Set.range I)
  let W' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm W (Set.range J)
  dsimp [φ, ψ, F', V', W']
  intro x hx hFx
  change fderivWithin 𝕜 F' (Set.range I) x (V' x) = W' (F' x)
  have hxRange : x ∈ Set.range I :=
    extChartAt_target_subset_range (I := I) (1 : G) hx
  have hUnique : UniqueMDiffWithinAt 𝓘(𝕜, EG) (Set.range I) x :=
    UniqueDiffWithinAt.uniqueMDiffWithinAt (I.uniqueDiffOn.uniqueDiffWithinAt hxRange)
  have hφdiff :
      MDifferentiableWithinAt 𝓘(𝕜, EG) I φ.symm (Set.range I) x :=
    mdifferentiableWithinAt_extChartAt_symm hx
  have hFdiff : MDifferentiableAt I J F (φ.symm x) :=
    hVW.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hψdiff :
      MDifferentiableAt J 𝓘(𝕜, EH) ψ (F (φ.symm x)) := by
    have hChartSource : F (φ.symm x) ∈ (chartAt HH (1 : H)).source := by
      simpa [ψ, extChartAt] using hFx
    simpa [ψ] using (mdifferentiableAt_extChartAt hChartSource)
  have hψleft : ψ.symm (ψ (F (φ.symm x))) = F (φ.symm x) :=
    PartialEquiv.left_inv ψ hFx
  have hTargetPullback :
      W' (F' x) = mfderiv% ψ (F (φ.symm x)) (W (F (φ.symm x))) := by
    -- Rewrite the target pullback in terms of the preferred target-chart derivative.
    dsimp [W', F']
    rw [VectorField.mpullbackWithin_apply, hψleft]
    exact congrArg (fun L : EH →L[𝕜] EH ↦ L (W (F (φ.symm x))))
      (targetChartInverseDerivativeAtOne (J := J) (H := H) (z := F (φ.symm x)) hFx)
  have hFcompDiff : MDifferentiableWithinAt 𝓘(𝕜, EG) J (F ∘ φ.symm) (Set.range I) x := by
    simpa [Function.comp] using hFdiff.comp_mdifferentiableWithinAt x hφdiff
  -- Route correction: perform the chain-rule normalization in one fixed chart spelling before
  -- applying the pointwise `f_related` identity.
  rw [hTargetPullback]
  dsimp [V']
  rw [VectorField.mpullbackWithin_apply]
  rw [← mfderivWithin_eq_fderivWithin]
  rw [mfderiv_comp_mfderivWithin (I := 𝓘(𝕜, EG)) (I' := J) (I'' := 𝓘(𝕜, EH))]
  · rw [mfderiv_comp_mfderivWithin_of_eq (I := 𝓘(𝕜, EG)) (I' := I) (I'' := J)
      hFdiff hφdiff hUnique rfl]
    change
      mfderiv% ψ (F (φ.symm x))
        (mfderiv I J F (φ.symm x)
          ((mfderiv[Set.range I] φ.symm x)
            ((mfderiv[Set.range I] φ.symm x).inverse (V (φ.symm x))))) =
        mfderiv% ψ (F (φ.symm x)) (W (F (φ.symm x)))
    rw [(isInvertible_mfderivWithin_extChartAt_symm (I := I) (x := (1 : G)) (y := x)
      hx).self_apply_inverse]
    rw [VectorField.f_related_apply hVW (φ.symm x)]
  · exact hψdiff
  · exact hFcompDiff
  · exact hUnique

/-- Helper for Definition 8.61-extra-1: an `F`-related pair of vector fields becomes an ordinary
chart-space pushforward identity near the preferred chart of `1`. -/
theorem chartPushforwardRelatedWithinAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {V : ∀ g : G, TangentSpace I g}
    {W : ∀ h : H, TangentSpace J h}
    (hVW : VectorField.f_related F V W) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let V' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm V (Set.range I)
    let W' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm W (Set.range J)
    (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (V' x))
      =ᶠ[nhdsWithin (φ (1 : G)) (Set.range I)] fun x ↦ W' (F' x) := by
  dsimp
  -- Wrap the pointwise chart identity into an eventual equality near the preferred chart of `1`.
  filter_upwards [self_mem_nhdsWithin,
    extChartAt_target_mem_nhdsWithin (I := I) (1 : G),
    chartMapEventuallyIntoTargetSourceAtOne (I := I) (J := J) (G := G) (H := H) F]
    with x hxRange hxTarget hxSource
  exact chartPushforwardRelatedWithinAtOnePointwise
    (I := I) (J := J) (G := G) (H := H) F hVW hxTarget hxSource

/-- Helper for Definition 8.61-extra-1: an eventual chart-space pushforward identity turns the
derivative term from `VectorField.fderivWithin_apply_lieBracket` into the derivative of the target
chart pullback composed with the chart map of `F`. -/
theorem chartPushforwardDerivativeTermAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H)
    {U Z : EG → EG} {U'' : EH → EH}
    (hU :
      let φ := extChartAt I (1 : G)
      let ψ := extChartAt J (1 : H)
      let F' := ψ ∘ F ∘ φ.symm
      let x0 := φ (1 : G)
      (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (U x))
        =ᶠ[nhdsWithin x0 (Set.range I)] fun x ↦ U'' (F' x))
    (hU'' :
      DifferentiableWithinAt 𝕜 U'' (Set.range J)
        ((extChartAt J (1 : H)) (1 : H))) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let x0 := φ (1 : G)
    fderivWithin 𝕜 (fun x ↦ fderivWithin 𝕜 F' (Set.range I) x (U x))
      (Set.range I) x0 (Z x0) =
      fderivWithin 𝕜 U'' (Set.range J) (F' x0)
        (fderivWithin 𝕜 F' (Set.range I) x0 (Z x0)) := by
  dsimp at hU ⊢
  have hx0 : ((extChartAt I (1 : G)) (1 : G)) ∈ Set.range I :=
    Set.mem_range_self _
  have hChart :
      ContDiffWithinAt 𝕜 ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target ((extChartAt I (1 : G)) (1 : G)) := by
    simpa using
      inducedLieAlgebraChartMapContDiffWithinAtOne (I := I) (J := J) (G := G) (H := H) F
  have hUnique : UniqueDiffWithinAt 𝕜 (Set.range I) ((extChartAt I (1 : G)) (1 : G)) :=
    I.uniqueDiffOn.uniqueDiffWithinAt hx0
  have hChartRange :
      ContDiffWithinAt 𝕜 ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) := by
    -- Restrict the chart-level smoothness of `F` from the chart target to `range I`.
    exact hChart.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin (I := I) (1 : G))
  have hFdiff :
      DifferentiableWithinAt 𝕜
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) :=
    hChartRange.differentiableWithinAt (by simp)
  have hMapsTo :
      Set.MapsTo
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) (Set.range J) := by
    -- The preferred target chart always lands in `range J`.
    exact fun x hx ↦ Set.mem_range_self _
  have hU''At :
      DifferentiableWithinAt 𝕜 U'' (Set.range J)
        (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          ((extChartAt I (1 : G)) (1 : G))) := by
    simpa [Function.comp, F.map_one] using hU''
  -- Rewrite the derivative target by eventual equality, then apply the within-set chain rule.
  rw [Filter.EventuallyEq.fderivWithin_eq_of_mem hU hx0]
  symm
  simpa [Function.comp] using
    (fderivWithin_fderivWithin (x := ((extChartAt I (1 : G)) (1 : G)))
      (y := (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        ((extChartAt I (1 : G)) (1 : G))))
      (g := U'') (f := ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm))
      (s := Set.range I) (t := Set.range J) hU''At hFdiff hMapsTo hUnique rfl _)

/-- Helper for Definition 8.61-extra-1: at the preferred charts of `1`, the chart map of `F`
sends the source Euclidean Lie bracket to the target Euclidean Lie bracket of the pushed-forward
invariant fields. -/
theorem inducedLieAlgebraBracketChartPushforwardAtOne
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    let φ := extChartAt I (1 : G)
    let ψ := extChartAt J (1 : H)
    let F' := ψ ∘ F ∘ φ.symm
    let X' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Xᴸ (Set.range I)
    let Y' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Yᴸ (Set.range I)
    let X'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
      ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J)
    let Y'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
      ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J)
    fderivWithin 𝕜 F' (Set.range I) (φ (1 : G))
      (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) (φ (1 : G))) =
      VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) (ψ (1 : H)) := by
  dsimp
  have hx0 : ((extChartAt I (1 : G)) (1 : G)) ∈ Set.range I :=
    Set.mem_range_self _
  have hChart :
      ContDiffWithinAt 𝕜 ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (extChartAt I (1 : G)).target ((extChartAt I (1 : G)) (1 : G)) := by
    simpa using
      inducedLieAlgebraChartMapContDiffWithinAtOne (I := I) (J := J) (G := G) (H := H) F
  have hx0Closure :
      ((extChartAt I (1 : G)) (1 : G)) ∈ closure (interior (Set.range I)) :=
    I.range_subset_closure_interior hx0
  have hChartRange :
      ContDiffWithinAt 𝕜 ∞
        ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) := by
    -- Work in the same chart spelling as the single-field pushforward lemmas.
    exact hChart.mono_of_mem_nhdsWithin (extChartAt_target_mem_nhdsWithin (I := I) (1 : G))
  have hSourceX :
      DifferentiableWithinAt 𝕜
        (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ (Set.range I))
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) :=
    sourceMulInvariantChartPullbackDifferentiableWithinAtOne (I := I) (G := G) X
  have hSourceY :
      DifferentiableWithinAt 𝕜
        (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ (Set.range I))
        (Set.range I) ((extChartAt I (1 : G)) (1 : G)) :=
    sourceMulInvariantChartPullbackDifferentiableWithinAtOne (I := I) (G := G) Y
  have hTargetX :
      DifferentiableWithinAt 𝕜
        (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
          ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
        (Set.range J) ((extChartAt J (1 : H)) (1 : H)) :=
    targetMulInvariantChartPullbackDifferentiableWithinAtOne (J := J) (H := H)
      (inducedLieAlgebraLinearMap F X)
  have hTargetY :
      DifferentiableWithinAt 𝕜
        (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
        (Set.range J) ((extChartAt J (1 : H)) (1 : H)) :=
    targetMulInvariantChartPullbackDifferentiableWithinAtOne (J := J) (H := H)
      (inducedLieAlgebraLinearMap F Y)
  have hXevt :
      (fun x ↦
        fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          (Set.range I) x
          ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
            (Set.range I)) x))
        =ᶠ[nhdsWithin ((extChartAt I (1 : G)) (1 : G)) (Set.range I)]
          fun x ↦
            (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
              (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm) x) := by
    simpa using
      chartPushforwardRelatedWithinAtOne (I := I) (J := J) (G := G) (H := H) F
        (V := Xᴸ) (W := ((inducedLieAlgebraLinearMap F X)ᴸ))
        (inducedLieAlgebraLinearMap_related (I := I) (J := J) (G := G) (H := H) F X)
  have hYevt :
      (fun x ↦
        fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          (Set.range I) x
          ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
            (Set.range I)) x))
        =ᶠ[nhdsWithin ((extChartAt I (1 : G)) (1 : G)) (Set.range I)]
          fun x ↦
            (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
              (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm) x) := by
    simpa using
      chartPushforwardRelatedWithinAtOne (I := I) (J := J) (G := G) (H := H) F
        (V := Yᴸ) (W := ((inducedLieAlgebraLinearMap F Y)ᴸ))
        (inducedLieAlgebraLinearMap_related (I := I) (J := J) (G := G) (H := H) F Y)
  have hX0 :
      fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          (Set.range I) ((extChartAt I (1 : G)) (1 : G))
          ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
            (Set.range I)) ((extChartAt I (1 : G)) (1 : G))) =
        (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
          ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
          (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
            ((extChartAt I (1 : G)) (1 : G))) :=
    hXevt.eq_of_nhdsWithin hx0
  have hY0 :
      fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          (Set.range I) ((extChartAt I (1 : G)) (1 : G))
          ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
            (Set.range I)) ((extChartAt I (1 : G)) (1 : G))) =
        (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
          (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
            ((extChartAt I (1 : G)) (1 : G))) :=
    hYevt.eq_of_nhdsWithin hx0
  have hF0 :
      ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
          ((extChartAt I (1 : G)) (1 : G)) =
        ((extChartAt J (1 : H)) (1 : H)) := by
    simp [Function.comp, F.map_one]
  -- Apply the Euclidean Lie-bracket formula once, then rewrite both derivative terms by the
  -- single-term adapter and collapse the basepoint values with the eventual equalities.
  calc
    fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
        (Set.range I) ((extChartAt I (1 : G)) (1 : G))
        (VectorField.lieBracketWithin 𝕜
          (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
            (Set.range I))
          (VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
            (Set.range I))
          (Set.range I) ((extChartAt I (1 : G)) (1 : G))) =
        fderivWithin 𝕜
            (fun x ↦
              fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
                (Set.range I) x
                ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
                  (Set.range I)) x))
            (Set.range I) ((extChartAt I (1 : G)) (1 : G))
            ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
              (Set.range I)) ((extChartAt I (1 : G)) (1 : G))) -
          fderivWithin 𝕜
            (fun x ↦
              fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
                (Set.range I) x
                ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
                  (Set.range I)) x))
            (Set.range I) ((extChartAt I (1 : G)) (1 : G))
            ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
              (Set.range I)) ((extChartAt I (1 : G)) (1 : G))) := by
      simpa using
        (VectorField.fderivWithin_apply_lieBracket (𝕜 := 𝕜)
          (f := ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm))
          (V := VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
            (Set.range I))
          (W := VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
            (Set.range I))
          (n := (∞ : ℕ∞ω)) hChartRange
          (by
            exact
              (minSmoothness_monotone (by norm_num : (2 : ℕ) ≤ 3)).trans
                (by simp : minSmoothness 𝕜 3 ≤ (∞ : ℕ∞ω)))
          I.uniqueDiffOn hx0Closure hx0 hSourceY hSourceX)
    _ =
        fderivWithin 𝕜
            (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
            (Set.range J)
            (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
              ((extChartAt I (1 : G)) (1 : G)))
            (fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
              (Set.range I) ((extChartAt I (1 : G)) (1 : G))
              ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
                (Set.range I)) ((extChartAt I (1 : G)) (1 : G)))) -
          fderivWithin 𝕜
            (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
            (Set.range J)
            (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
              ((extChartAt I (1 : G)) (1 : G)))
            (fderivWithin 𝕜 ((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
              (Set.range I) ((extChartAt I (1 : G)) (1 : G))
              ((VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
                (Set.range I)) ((extChartAt I (1 : G)) (1 : G)))) := by
      rw [chartPushforwardDerivativeTermAtOne (I := I) (J := J) (G := G) (H := H) (F := F)
        (U := VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
          (Set.range I))
        (U'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
        (Z := VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
          (Set.range I)) hYevt hTargetY]
      rw [chartPushforwardDerivativeTermAtOne (I := I) (J := J) (G := G) (H := H) (F := F)
        (U := VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Xᴸ
          (Set.range I))
        (U'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
          ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
        (Z := VectorField.mpullbackWithin 𝓘(𝕜, EG) I (extChartAt I (1 : G)).symm Yᴸ
          (Set.range I)) hXevt hTargetX]
    _ =
        fderivWithin 𝕜
            (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
            (Set.range J)
            (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
              ((extChartAt I (1 : G)) (1 : G)))
            ((VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
              (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
                ((extChartAt I (1 : G)) (1 : G)))) -
          fderivWithin 𝕜
            (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
            (Set.range J)
            (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
              ((extChartAt I (1 : G)) (1 : G)))
            ((VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
              ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
              (((extChartAt J (1 : H)) ∘ F ∘ (extChartAt I (1 : G)).symm)
                ((extChartAt I (1 : G)) (1 : G)))) := by
      rw [hX0, hY0]
    _ = VectorField.lieBracketWithin 𝕜
          (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
            ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J))
          (VectorField.mpullbackWithin 𝓘(𝕜, EH) J (extChartAt J (1 : H)).symm
            ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J))
          (Set.range J) ((extChartAt J (1 : H)) (1 : H)) := by
      rw [VectorField.lieBracketWithin_eq, hF0]

/-- Helper for Definition 8.61-extra-1: at the identity, `mfderiv I J F 1` sends the source
manifold bracket of invariant fields to the target manifold bracket of the pushed-forward
invariant fields. -/
theorem inducedLieAlgebraLinearMap_mlieBracket_apply_one
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G)) =
      VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
        ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H) := by
  -- Route correction: the broken `Sec08_59/Proposition_8_30` import forced the chart argument to
  -- live locally in this file. The remaining step is now a chart-cancellation argument around
  -- the explicit Euclidean bracket transport at `1`.
  let φ := extChartAt I (1 : G)
  let ψ := extChartAt J (1 : H)
  let F' := ψ ∘ F ∘ φ.symm
  let X' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Xᴸ (Set.range I)
  let Y' := VectorField.mpullbackWithin 𝓘(𝕜, EG) I φ.symm Yᴸ (Set.range I)
  let X'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
    ((inducedLieAlgebraLinearMap F X)ᴸ) (Set.range J)
  let Y'' := VectorField.mpullbackWithin 𝓘(𝕜, EH) J ψ.symm
    ((inducedLieAlgebraLinearMap F Y)ᴸ) (Set.range J)
  let x0 := φ (1 : G)
  have hx0Target : x0 ∈ φ.target := by
    simpa [φ, x0] using mem_extChartAt_target (1 : G)
  have hSourceDeriv :
      mfderiv[Set.range I] φ.symm x0 = (mfderiv% φ (1 : G)).inverse := by
    -- The source chart inverse derivative is the inverse of the preferred chart derivative at `1`.
    apply ContinuousLinearMap.inverse_eq
    · simpa [φ, x0] using
        mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt
          (I := I) (x := (1 : G)) (y := x0) hx0Target
    · simpa [φ, x0] using
        mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm
          (I := I) (x := (1 : G)) (y := x0) hx0Target
  have hφdiff :
      MDifferentiableWithinAt 𝓘(𝕜, EG) I φ.symm (Set.range I) x0 := by
    simpa [φ, x0] using mdifferentiableWithinAt_extChartAt_symm hx0Target
  have hFdiff : MDifferentiableAt I J F (φ.symm x0) := by
    simpa [φ, x0] using
      F.contMDiff_toFun.contMDiffAt.mdifferentiableAt (x := (1 : G)) (by simp)
  have hUnique :
      UniqueMDiffWithinAt 𝓘(𝕜, EG) (Set.range I) x0 :=
    UniqueDiffWithinAt.uniqueMDiffWithinAt
      (I.uniqueDiffOn.uniqueDiffWithinAt (Set.mem_range_self _))
  have hψdiff :
      MDifferentiableAt J 𝓘(𝕜, EH) ψ (F (φ.symm x0)) := by
    have hChartSource : F (φ.symm x0) ∈ (chartAt HH (1 : H)).source := by
      simpa [φ, ψ, x0, extChartAt, F.map_one] using mem_extChartAt_source (I := J) (1 : H)
    simpa [ψ] using (mdifferentiableAt_extChartAt (I := J) hChartSource)
  have hFcompDiff :
      MDifferentiableWithinAt 𝓘(𝕜, EG) J (F ∘ φ.symm) (Set.range I) x0 := by
    simpa [Function.comp, φ, x0] using hFdiff.comp_mdifferentiableWithinAt x0 hφdiff
  have hLeft :
      mfderiv% ψ (F (1 : G))
          (mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G))) =
        fderivWithin 𝕜 F' (Set.range I) x0
          (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0) := by
    have hSourceBracket :
        VectorField.mlieBracket I Xᴸ Yᴸ (1 : G) =
          mfderiv[Set.range I] φ.symm x0
            (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0) := by
      -- Rewrite the source manifold bracket by the preferred-chart formula at `1`.
      simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply, Set.preimage_univ,
        Set.univ_inter, φ, x0, X', Y']
      rw [hSourceDeriv]
    -- Rewrite the source manifold bracket in preferred-chart form, then use the chart chain rule.
    calc
      mfderiv% ψ (F (1 : G))
          (mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G))) =
        mfderiv% ψ (F (1 : G))
          (mfderiv I J F (1 : G) (mfderiv[Set.range I] φ.symm x0
            (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0))) := by
          rw [hSourceBracket]
      _ = fderivWithin 𝕜 F' (Set.range I) x0
            (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0) := by
          symm
          rw [← mfderivWithin_eq_fderivWithin]
          rw [mfderiv_comp_mfderivWithin (I := 𝓘(𝕜, EG)) (I' := J) (I'' := 𝓘(𝕜, EH))]
          · rw [mfderiv_comp_mfderivWithin_of_eq (I := 𝓘(𝕜, EG)) (I' := I) (I'' := J)
              hFdiff hφdiff hUnique rfl]
            simp [F', φ, ψ, x0]
          · exact hψdiff
          · exact hFcompDiff
          · exact hUnique
  have hRight :
      mfderiv% ψ (1 : H)
          (VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
            ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H)) =
        VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) (ψ (1 : H)) := by
    -- Rewrite the target manifold bracket in preferred-chart form and cancel the chart inverse.
    simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_apply, Set.preimage_univ,
      Set.univ_inter, ψ, X'', Y'']
    exact
      (isInvertible_mfderiv_extChartAt (I := J) (x := (1 : H)) (y := (1 : H))
        (mem_extChartAt_source (I := J) (1 : H))).self_apply_inverse _
  -- Push both sides into the preferred target chart, substitute the Euclidean bracket transport,
  -- and cancel the chart derivative there.
  apply
    (isInvertible_mfderiv_extChartAt (I := J) (x := (1 : H)) (y := F (1 : G))
      (by simpa [F.map_one] using mem_extChartAt_source (I := J) (1 : H))).injective
  calc
    mfderiv% (extChartAt J (1 : H)) (F (1 : G))
        (mfderiv I J F (1 : G) (VectorField.mlieBracket I Xᴸ Yᴸ (1 : G))) =
      fderivWithin 𝕜 F' (Set.range I) x0
        (VectorField.lieBracketWithin 𝕜 X' Y' (Set.range I) x0) := by
        simpa [ψ] using hLeft
    _ = VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) (ψ (1 : H)) := by
        simpa [φ, ψ, F', X', Y', X'', Y''] using
          inducedLieAlgebraBracketChartPushforwardAtOne
            (I := I) (J := J) (G := G) (H := H) F X Y
    _ =
      mfderiv% (extChartAt J (1 : H)) (F (1 : G))
        (VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
          ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H)) := by
        have hRight' :
            VectorField.lieBracketWithin 𝕜 X'' Y'' (Set.range J) (ψ (1 : H)) =
              mfderiv% (extChartAt J (1 : H)) (F (1 : G))
                (VectorField.mlieBracket J ((inducedLieAlgebraLinearMap F X)ᴸ)
                  ((inducedLieAlgebraLinearMap F Y)ᴸ) (1 : H)) := by
          simpa [ψ, F.map_one] using hRight.symm
        exact hRight'

/-- Helper for Definition 8.61-extra-1: the derivative-at-identity linear map preserves the Lie
bracket because its associated left-invariant vector fields are `F`-related. -/
-- Route correction: the invariant-field pushforward is now isolated as
-- `inducedLieAlgebraLinearMap_related`, and the final Lie-algebra equality is isolated in
-- `inducedLieAlgebraLinearMap_mlieBracket_apply_one`. The remaining blocker is the pointwise
-- preferred-chart pushforward computation for the manifold bracket at `1`; importing the earlier
-- Section 8.59 bridge is not currently viable because that file does not compile in this
-- workspace.
theorem inducedLieAlgebraLinearMap_map_lie
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X Y : GroupLieAlgebra I G) :
    inducedLieAlgebraLinearMap F ⁅X, Y⁆ =
      ⁅inducedLieAlgebraLinearMap F X, inducedLieAlgebraLinearMap F Y⁆ := by
  -- Reduce the Lie-algebra statement to the manifold bracket identity at `1`.
  simpa [GroupLieAlgebra.bracket_def, inducedLieAlgebraLinearMap_apply] using
    inducedLieAlgebraLinearMap_mlieBracket_apply_one F X Y

/-- Definition 8.61-extra-1: for a smooth Lie group homomorphism `F : G → H`, the induced Lie
algebra homomorphism `F_* : GroupLieAlgebra I G →ₗ⁅𝕜⁆ GroupLieAlgebra J H` is the derivative of
`F` at the identity. -/
noncomputable def inducedLieAlgebraHomomorphism
    (F : ContMDiffMonoidMorphism I J ∞ G H) :
    GroupLieAlgebra I G →ₗ⁅𝕜⁆ GroupLieAlgebra J H where
  -- The linear part is the transported derivative at the identity.
  toLinearMap := inducedLieAlgebraLinearMap F
  -- Bracket compatibility comes from naturality of the Lie bracket under `f_related`.
  map_lie' := fun {x y} ↦ inducedLieAlgebraLinearMap_map_lie F x y

/- Source-facing notation for the induced Lie algebra homomorphism `F_*`. -/
scoped notation:max F "_*" => inducedLieAlgebraHomomorphism F
scoped notation:max F "_* " X => inducedLieAlgebraHomomorphism F X
scoped notation:max "(" F ")" "_*" => inducedLieAlgebraHomomorphism F
scoped notation:max "(" F ")" "_* " X => inducedLieAlgebraHomomorphism F X

end ContMDiffMonoidMorphism

open scoped ContMDiffMonoidMorphism

namespace ContMDiffMonoidMorphism

/-- For `X : GroupLieAlgebra I G`, the left-invariant vector field
`(F_* X)ᴸ` on `H` is `F`-related to the left-invariant vector field
`Xᴸ` on `G`, so the induced field is defined without assuming that `F` is a diffeomorphism. -/
theorem inducedLieAlgebraHomomorphism_related
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) :
    VectorField.f_related F Xᴸ
      (((F)_* X)ᴸ) := by
  -- The public theorem is the same `f_related` bridge, now reused through the linear-map helper.
  simpa [inducedLieAlgebraHomomorphism] using inducedLieAlgebraLinearMap_related F X

/- Pointwise derivative form of `inducedLieAlgebraHomomorphism_related`. -/
theorem inducedLieAlgebraHomomorphism_related_apply
    (F : ContMDiffMonoidMorphism I J ∞ G H) (X : GroupLieAlgebra I G) (g : G) :
    mfderiv I J F g (Xᴸ g) =
      (((F)_* X)ᴸ) (F g) :=
  VectorField.f_related_apply (inducedLieAlgebraHomomorphism_related F X) g

end ContMDiffMonoidMorphism
