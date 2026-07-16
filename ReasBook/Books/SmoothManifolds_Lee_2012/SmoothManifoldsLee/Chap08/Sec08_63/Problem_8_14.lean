import Mathlib
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_57.Definition_8_57_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Domain sampling:
-- * primary domain: smooth vector fields on manifolds and their relatedness along smooth maps;
-- * core/canonical owners sampled before refinement:
--   `C^∞⟮I, M; J, N⟯` for bundled smooth maps,
--   `Cₛ^∞⟮I; E, TangentSpace I⟯` for smooth vector fields,
--   `VectorField.f_related` for the source-facing relatedness predicate;
-- * bridge data: the graph-related rough vector field, whose smoothness is a derived fact.
-- The graph construction uses only `mfderiv`, product manifolds, bundled smooth maps/sections,
-- and the chapter owner `VectorField.f_related`, so no finite-dimensional ambient hypothesis
-- belongs in this file.

universe u𝕜 uE uE' uH uH' uM uN

noncomputable section

section

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type uH} [TopologicalSpace H]
  {H' : Type uH'} [TopologicalSpace H']
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
  {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 E' H'}
  [IsManifold I ∞ M]
  [IsManifold J ∞ N]

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun x : M ↦ TangentSpace I x⟯
local notation "SmoothProductVectorField" =>
  Cₛ^∞⟮I.prod J; E × E', fun p : M × N ↦ TangentSpace (I.prod J) p⟯
local notation "SmoothMap" => C^∞⟮I, M; J, N⟯

namespace VectorField

/-- The vector field on `M × N` whose first component is `X` and whose second component is
`mfderiv I J f x (X x)`, pulled back constantly along the `N`-factor. -/
@[simp]
def graphRelated (f : M → N) (X : ∀ x : M, TangentSpace I x) :
    ∀ p : M × N, TangentSpace (I.prod J) p :=
  fun p ↦ (X p.1, mfderiv I J f p.1 (X p.1))

/-- Helper for Problem 8-14: pushing the section `T% X` forward by `tangentMap I J f` and then
pulling it back along `Prod.fst` gives a smooth section of `TN` over `f ∘ Prod.fst`. -/
lemma graphDerivativeSectionAlongFst_contMDiff
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) :
    ContMDiff (I.prod J) J.tangent ∞
      (fun p : M × N ↦ tangentMap I J f (T% X p.1)) := by
  -- Smoothness comes from the bundled tangent map of `f` composed with the smooth first-factor
  -- section `p ↦ T% X p.1`.
  have htangent :
      ContMDiff I.tangent J.tangent ∞ (tangentMap I J f) := by
    simpa using f.contMDiff.contMDiff_tangentMap (m := (∞ : ℕ∞ω)) (by simp)
  simpa [Function.comp] using htangent.comp (hX.comp contMDiff_fst)

/-- Helper for Problem 8-14: near `p₀`, the graph transport written in tangent coordinates is the
composition of the target chart derivative and the inverse source chart derivative. -/
lemma graphTransportIdentityInCoordinates_eventuallyEq
    (f : SmoothMap) (p0 : M × N) :
    (fun p : M × N ↦
      inTangentCoordinates J J (fun q : M × N ↦ f q.1) Prod.snd
        (fun _ ↦ (1 : E' →L[𝕜] E')) p0 p) =ᶠ[nhds p0]
      fun p ↦
        (mfderiv% (extChartAt J p0.2) p.2) ∘L
          (mfderiv[Set.range J] (extChartAt J (f p0.1)).symm
            (extChartAt J (f p0.1) (f p.1))) := by
  -- Near `p0`, the first base map stays in the source chart around `f p0.1`.
  have hfst :
      {p : M × N | f p.1 ∈ (chartAt H' (f p0.1)).source} ∈ nhds p0 := by
    have hcont :
        ContinuousAt (fun p : M × N ↦ f p.1) p0 :=
      ((f.contMDiff.comp
          (contMDiff_fst : ContMDiff (I.prod J) I ∞ (Prod.fst : M × N → M))) p0).continuousAt
    simpa [Function.comp] using
      hcont.preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) (f p0.1))
  -- Near `p0`, the second projection stays in the source chart around `p0.2`.
  have hsnd :
      {p : M × N | p.2 ∈ (chartAt H' p0.2).source} ∈ nhds p0 := by
    have hcont : ContinuousAt (Prod.snd : M × N → N) p0 :=
      (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0).continuousAt
    simpa using hcont.preimage_mem_nhds (extChartAt_source_mem_nhds (I := J) p0.2)
  -- On that neighborhood, the coordinate transport is exactly the chart-derivative sandwich.
  filter_upwards [hfst, hsnd] with p hp1 hp2
  simpa using
    (inTangentCoordinates_eq_mfderiv_comp
      (I := J) (I' := J) (f := fun q : M × N ↦ f q.1) (g := Prod.snd)
      (ϕ := fun _ ↦ (1 : E' →L[𝕜] E')) (x₀ := p0) (x := p) hp1 hp2)

/-- Helper for Problem 8-14: in tangent coordinates around `(f p₀.1, p₀.2)`, the identity map
between the source and target tangent fibers varies smoothly along the graph base map. -/
lemma graphTransportIdentityInCoordinates_contMDiffAt
    (f : SmoothMap) (p0 : M × N) :
    ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
      (fun p : M × N ↦
        inTangentCoordinates J J (fun q : M × N ↦ f q.1) Prod.snd
          (fun _ ↦ (1 : E' →L[𝕜] E')) p0 p) p0 := by
  -- Route correction: the local rewrite to the raw chart-derivative sandwich is now isolated in
  -- `graphTransportIdentityInCoordinates_eventuallyEq`. The remaining blocker is proving smooth
  --ness of the two factors in the exact raw normal form used by that rewrite.
  -- TODO: upgrade the target factor via `ContMDiffAt.mfderiv_const` and the source factor via
  -- `ContMDiffWithinAt.mfderivWithin_const`, then combine them with `ContMDiffAt.clm_comp` and
  -- `graphTransportIdentityInCoordinates_eventuallyEq`.
  sorry

/-- Helper for Problem 8-14: the derivative section over `f ∘ Prod.fst` can be reused pointwise
at a fixed base point when applying the transport operator. -/
lemma graphDerivativeSectionAlongPairBase_contMDiffAt
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) (p0 : M × N) :
    ContMDiffAt (I.prod J) J.tangent ∞
      (fun p : M × N ↦
        (⟨f p.1, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) p0 := by
  -- The already-smooth tangent map section can be reused unchanged at the chosen base point.
  simpa [tangentMap, Function.comp] using
    (graphDerivativeSectionAlongFst_contMDiff (I := I) (J := J) f hX).contMDiffAt

/-- Helper for Problem 8-14: the `N`-component of `graphRelated f X` is the derivative section
based at `Prod.snd`. -/
lemma graphRelatedSecondComponent_contMDiff
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) :
    ContMDiff (I.prod J) J.tangent ∞
      (fun p : M × N ↦
        (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) := by
  intro p0
  let b₁ : M × N → N := fun p ↦ f p.1
  let b₂ : M × N → N := Prod.snd
  let ϕ : ∀ p : M × N, TangentSpace J (b₁ p) →L[𝕜] TangentSpace J (b₂ p) :=
    fun _ ↦ (ContinuousLinearMap.id 𝕜 E' : E' →L[𝕜] E')
  let v : ∀ p : M × N, TangentSpace J (b₁ p) := fun p ↦ mfderiv I J f p.1 (X p.1)
  have hϕ :
      ContMDiffAt (I.prod J) 𝓘(𝕜, E' →L[𝕜] E') ∞
        (fun p : M × N ↦ inTangentCoordinates J J b₁ b₂ ϕ p0 p) p0 := by
    -- This is the only genuine transport step: the coordinate form of the identity map between
    -- tangent fibers must vary smoothly with both base points.
    simpa [b₁, b₂, ϕ] using graphTransportIdentityInCoordinates_contMDiffAt (J := J) f p0
  have hv :
      ContMDiffAt (I.prod J) J.tangent ∞ (fun p : M × N ↦ (v p : TangentBundle J N)) p0 := by
    -- Reuse the previously proved smooth derivative section without reopening the tangent-map
    -- regularity argument.
    simpa [b₁, v] using graphDerivativeSectionAlongPairBase_contMDiffAt (I := I) (J := J) f hX p0
  have hb₂ : ContMDiffAt (I.prod J) J ∞ b₂ p0 := by
    -- The target base map is just the second projection.
    simpa [b₂] using (contMDiffAt_snd : ContMDiffAt (I.prod J) J ∞ (Prod.snd : M × N → N) p0)
  -- Apply the smooth transport family to the smooth derivative section.
  simpa [b₁, b₂, ϕ, v] using (ContMDiffAt.clm_apply_of_inCoordinates hϕ hv hb₂)

/-- Helper for Problem 8-14: under the product tangent-bundle equivalence, `graphRelated f X`
splits into the original section `X` and the derivative section over `N`. -/
lemma equivTangentBundleProd_graphRelated_apply
    (f : SmoothMap) (X : ∀ x : M, TangentSpace I x) (p : M × N) :
    equivTangentBundleProd I M J N (T% (graphRelated f X) p) =
      (T% X p.1, (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) := by
  -- Expanding `graphRelated` shows that the product tangent-bundle equivalence just separates the
  -- two components.
  rcases p with ⟨x, y⟩
  rfl

/-- The explicit vector field on `M × N` attached to `f` and `X` is smooth when `f` and `X`
are smooth. -/
theorem contMDiff_graphRelated
    (f : SmoothMap) {X : ∀ x : M, TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (T% X)) :
    ContMDiff (I.prod J) (I.prod J).tangent ∞
      (T% ((graphRelated f X : ∀ p : M × N, TangentSpace (I.prod J) p))) :=
  by
    -- Route correction: separate the product tangent-bundle components first, so the remaining
    -- work is only the transport from base `f ∘ Prod.fst` to base `Prod.snd` in the `N`-part.
    let F : M × N → TangentBundle I M × TangentBundle J N := fun p ↦
      (T% X p.1, (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N))
    have hF : ContMDiff (I.prod J) (I.tangent.prod J.tangent) ∞ F := by
      -- Each component is smooth after pulling back along the corresponding projection.
      have hfirst : ContMDiff (I.prod J) I.tangent ∞ (fun p : M × N ↦ T% X p.1) := by
        simpa using hX.comp contMDiff_fst
      have hsecond :
          ContMDiff (I.prod J) J.tangent ∞
            (fun p : M × N ↦
              (⟨p.2, mfderiv I J f p.1 (X p.1)⟩ : TangentBundle J N)) :=
        graphRelatedSecondComponent_contMDiff f hX
      simpa [F, Function.comp] using hfirst.prodMk hsecond
    have htransport :
        ContMDiff (I.prod J) (I.prod J).tangent ∞
          ((equivTangentBundleProd I M J N).symm ∘ F) := by
      -- Transport the smooth pair of tangent-bundle sections back to the tangent bundle of
      -- the product manifold.
      exact
        (contMDiff_equivTangentBundleProd_symm
          (I := I) (I' := J) (M := M) (M' := N)).comp hF
    have hEq : ((equivTangentBundleProd I M J N).symm ∘ F) =
        T% ((graphRelated f X : ∀ p : M × N, TangentSpace (I.prod J) p)) := by
      -- The forward bundle equivalence identifies the transported pair with `graphRelated f X`.
      funext p
      apply (equivTangentBundleProd I M J N).injective
      simpa [F, Function.comp] using equivTangentBundleProd_graphRelated_apply f X p
    exact hEq ▸ htransport

/-- Helper for Problem 8-14: differentiating the graph map `x ↦ (x, f x)` applies `X x` to the
product derivative componentwise. -/
lemma graphMapMfderiv_apply
    (f : SmoothMap) (X : ∀ x : M, TangentSpace I x) (x : M) :
    mfderiv I (I.prod J) (fun y : M ↦ (y, f y)) x (X x) =
      graphRelated f X (x, f x) := by
  -- Differentiate the two graph-map coordinates separately and repackage the result.
  rw [mfderiv_prodMk]
  · rw [graphRelated]
    change
      ((((mfderiv I I (fun y : M ↦ y) x) (X x)), mfderiv I J f x (X x)) :
        TangentSpace (I.prod J) (x, f x)) =
        (X x, mfderiv I J f x (X x))
    change (((mfderiv I I (@id M) x) (X x)), mfderiv I J f x (X x)) =
        (X x, mfderiv I J f x (X x))
    rw [mfderiv_id]
    rfl
  · exact mdifferentiableAt_id
  · exact f.contMDiff.mdifferentiableAt (by simp)

/-- Along the graph map `x ↦ (x, f x)`, the explicit vector field on `M × N` is related to `X`. -/
theorem graphMap_f_related_graphRelated
    (f : SmoothMap) (X : ∀ x : M, TangentSpace I x) :
    f_related
      ((fun x : M ↦ (x, f x)) : M → M × N)
      X
      (graphRelated f X : ∀ p : M × N, TangentSpace (I.prod J) p) :=
  by
    constructor
    · -- The graph map is smooth because each coordinate is smooth.
      simpa using contMDiff_id.prodMk f.contMDiff
    · intro x
      -- The relatedness identity is exactly the graph-map derivative formula.
      simpa using graphMapMfderiv_apply f X x

/-- The canonical bundled smooth vector field on `M × N` attached to a smooth map `f` and a
smooth vector field `X` on `M`. -/
def graphRelatedSmooth
    (f : SmoothMap) (X : SmoothVectorField) :
    SmoothProductVectorField :=
  ⟨graphRelated f X, contMDiff_graphRelated f X.contMDiff⟩

/-- The bundled graph-related vector field is related to `X` along the graph map. -/
theorem graphMap_f_related_graphRelatedSmooth
    (f : SmoothMap) (X : SmoothVectorField) :
    f_related
      (fun x : M ↦ (x, f x))
      X
      (graphRelatedSmooth f X) :=
  graphMap_f_related_graphRelated f X

end VectorField

/-- Problem 8-14: if `f : M → N` is smooth and `X` is a smooth vector field on `M`, then there
exists a smooth vector field on `M × N` whose value along the graph map `F(x) = (x, f x)` is
`mfderiv I (I.prod J) F x (X x)`. -/
theorem exists_smooth_graph_related_vector_field
    (f : SmoothMap) (X : SmoothVectorField) :
    ∃ Y : SmoothProductVectorField,
      VectorField.f_related
        (fun x : M ↦ (x, f x))
        X
        Y :=
  ⟨VectorField.graphRelatedSmooth f X, VectorField.graphMap_f_related_graphRelatedSmooth f X⟩

end
