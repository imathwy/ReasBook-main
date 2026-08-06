import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Homotopy.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Definition_7_4_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Bundle

universe u v w

-- Semantic recall via `lean_leansearch`: `ContinuousMap.Homotopic` is the canonical homotopy
-- relation on maps, and Chapter 23 already packages equivalence of real plane bundles over a
-- fixed base as `RealPlaneBundleIso`.

section

variable {X : Type u} [TopologicalSpace X]
variable {B : Type v} [TopologicalSpace B]
variable {n : ℕ}
variable {E : B → Type w}
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]

/-- The identity data gives a bundle isomorphism from a real `n`-plane bundle to itself. -/
private def realPlaneBundleIsoRefl
    (B : Type u) [TopologicalSpace B] (E : B → Type v)
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)] :
    RealPlaneBundleIso n B E E where
  toContinuousLinearEquiv b := ContinuousLinearEquiv.refl ℝ (E b)
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- Bundle isomorphisms can be reversed fiberwise. -/
private def realPlaneBundleIsoSymm
    {E E' : B → Type w}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E')]
    [∀ b, TopologicalSpace (E b)] [∀ b, TopologicalSpace (E' b)]
    [∀ b, AddCommGroup (E b)] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℝ (E b)] [∀ b, Module ℝ (E' b)]
    (η : RealPlaneBundleIso n B E E') :
    RealPlaneBundleIso n B E' E where
  toContinuousLinearEquiv b := (η.toContinuousLinearEquiv b).symm
  continuous_toFun := η.continuous_invFun
  continuous_invFun := η.continuous_toFun

/-- Bundle isomorphisms compose fiberwise. -/
private def realPlaneBundleIsoTrans
    {E₀ E₁ E₂ : B → Type w}
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E₀)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E₁)]
    [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E₂)]
    [∀ b, TopologicalSpace (E₀ b)] [∀ b, TopologicalSpace (E₁ b)] [∀ b, TopologicalSpace (E₂ b)]
    [∀ b, AddCommGroup (E₀ b)] [∀ b, AddCommGroup (E₁ b)] [∀ b, AddCommGroup (E₂ b)]
    [∀ b, Module ℝ (E₀ b)] [∀ b, Module ℝ (E₁ b)] [∀ b, Module ℝ (E₂ b)]
    (η₀₁ : RealPlaneBundleIso n B E₀ E₁) (η₁₂ : RealPlaneBundleIso n B E₁ E₂) :
    RealPlaneBundleIso n B E₀ E₂ where
  toContinuousLinearEquiv b := (η₀₁.toContinuousLinearEquiv b).trans (η₁₂.toContinuousLinearEquiv b)
  continuous_toFun := η₁₂.continuous_toFun.comp η₀₁.continuous_toFun
  continuous_invFun := η₀₁.continuous_invFun.comp η₁₂.continuous_invFun

/-- Helper for Proposition 23.1.3: if `f` lands in `e.baseSet`, then the pullback trivialization
has source all of the pullback total space. -/
private lemma pullbackTrivializationSourceEqUniv
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hf : ∀ x : X, f x ∈ e.baseSet) :
    (e.pullback f).source = Set.univ := by
  -- The pullback source is the preimage of `e.source`, so pointwise membership in `e.baseSet`
  -- makes every pullback point land in the source.
  ext z
  simp [e.source_eq, hf z.1]

/-- Helper for Proposition 23.1.3: if `f` lands in `e.baseSet`, then the pullback base set is all
of `X`. -/
private lemma pullbackTrivializationBaseSetEqUniv
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hf : ∀ x : X, f x ∈ e.baseSet) :
    (e.pullback f).baseSet = Set.univ := by
  -- The pullback base set is exactly `f ⁻¹' e.baseSet`.
  ext x
  simp [hf x]

/-- Helper for Proposition 23.1.3: if `f` lands in `e.baseSet`, then the pullback trivialization
has target all of `X × (Fin n → ℝ)`. -/
private lemma pullbackTrivializationTargetEqUniv
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hf : ∀ x : X, f x ∈ e.baseSet) :
    (e.pullback f).target = Set.univ := by
  -- Once the pullback base set is all of `X`, the target product set is all of `X × F`.
  ext y
  simp [hf y.1]

/-- Helper for Proposition 23.1.3: the inverse of a pulled-back linear trivialization is the
fiberwise inverse continuous linear equivalence on the pullback fiber. -/
private lemma pullbackTrivializationSymm_apply
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    {x : X} (hx : x ∈ (e.pullback f).baseSet) (v : Fin n → ℝ) :
    (e.pullback f).toOpenPartialHomeomorph.symm (x, v) =
      @Bundle.TotalSpace.mk X (Fin n → ℝ) (f *ᵖ E) x
        (((e.pullback f).continuousLinearEquivAt ℝ x hx).symm v) := by
  -- This is the pullback specialization of the standard inverse-trivialization normal form.
  simpa using
    (@Bundle.Trivialization.symm_apply_eq_mk_continuousLinearEquivAt_symm
      ℝ X (Fin n → ℝ) (f *ᵖ E)
      inferInstance
      inferInstance
      (continuousMapCoePullbackModules f E)
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      inferInstance
      (e.pullback f)
      inferInstance
      x hx v)

/-- Helper for Proposition 23.1.3: a pullback trivialization whose base set is all of `X`
upgrades to a total-space homeomorphism. -/
private noncomputable def globalPullbackTrivializationHomeomorph
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf : ∀ x : X, f x ∈ e.baseSet) :
    Bundle.TotalSpace (Fin n → ℝ) (f *ᵖ E) ≃ₜ X × (Fin n → ℝ) :=
  -- The pulled-back chart is globally defined, so its underlying open partial homeomorphism
  -- upgrades to an honest homeomorphism of the total spaces.
  (e.pullback f).toOpenPartialHomeomorph.toHomeomorphOfSourceEqUnivTargetEqUniv
    (pullbackTrivializationSourceEqUniv e hf)
    (pullbackTrivializationTargetEqUniv e hf)

/-- Helper for Proposition 23.1.3: the global pullback-trivialization homeomorphism agrees with
the fiberwise chart formula. -/
private lemma globalPullbackTrivializationHomeomorph_apply
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf : ∀ x : X, f x ∈ e.baseSet)
    (z : Bundle.TotalSpace (Fin n → ℝ) (f *ᵖ E)) :
    globalPullbackTrivializationHomeomorph e hf z =
      (z.1, (e.pullback f).continuousLinearEquivAt ℝ z.1
        (hf z.1) z.2) := by
  -- Route correction: instead of unfolding the `RealPlaneBundleIso` package directly, first
  -- normalize the total-space map through the global homeomorphism supplied by the chart.
  rw [Bundle.Trivialization.continuousLinearEquivAt_apply' (e.pullback f) z
    (by simpa [Bundle.Trivialization.source_eq] using hf z.1)]
  rfl

/-- Helper for Proposition 23.1.3: the inverse global pullback-trivialization homeomorphism agrees
with the inverse fiberwise chart formula. -/
private lemma globalPullbackTrivializationHomeomorph_symm_apply
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf : ∀ x : X, f x ∈ e.baseSet)
    (x : X) (v : Fin n → ℝ) :
    (globalPullbackTrivializationHomeomorph e hf).symm (x, v) =
      @Bundle.TotalSpace.mk X (Fin n → ℝ) (f *ᵖ E) x
        (((e.pullback f).continuousLinearEquivAt ℝ x (hf x)).symm v) := by
  -- The upgraded homeomorphism has the same inverse map as the underlying pulled-back
  -- trivialization, so the standard vector-bundle inverse normal form applies unchanged.
  simpa [globalPullbackTrivializationHomeomorph] using
    (pullbackTrivializationSymm_apply e (hf x) v)

/-- Helper for Proposition 23.1.3: the fiber map of a pulled-back linear trivialization can be
referred to with the coercion-shaped pullback module instances made explicit. -/
private noncomputable def pullbackTrivializationContinuousLinearEquiv
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (x : X) (hx : f x ∈ e.baseSet) :
    ((⇑f *ᵖ E) x) ≃L[ℝ] (Fin n → ℝ) :=
  @Bundle.Trivialization.continuousLinearEquivAt ℝ X (Fin n → ℝ) (⇑f *ᵖ E)
    inferInstance
    inferInstance
    (continuousMapCoePullbackModules f E)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (e.pullback f)
    inferInstance
    x
    hx

/-- Helper for Proposition 23.1.3: the explicit pullback fiber map is definitionally the usual
`continuousLinearEquivAt` map. -/
private lemma pullbackTrivializationContinuousLinearEquiv_apply
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (x : X) (hx : f x ∈ e.baseSet) (v : (⇑f *ᵖ E) x) :
    pullbackTrivializationContinuousLinearEquiv e x hx v =
      (e.pullback f).continuousLinearEquivAt ℝ x hx v := rfl

/-- Helper for Proposition 23.1.3: the inverse of the explicit pullback fiber map is the pulled
back trivialization inverse. -/
private lemma pullbackTrivializationContinuousLinearEquiv_symm_apply
    {f : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (x : X) (hx : f x ∈ e.baseSet) (v : Fin n → ℝ) :
    (pullbackTrivializationContinuousLinearEquiv e x hx).symm v =
      ((e.pullback f).continuousLinearEquivAt ℝ x hx).symm v := rfl

/-- Helper for Proposition 23.1.3: a single global linear trivialization identifies the two
endpoint pullback fibers by composing the two chart maps through `Fin n → ℝ`. -/
private noncomputable def globalPullbackFiberLinearEquiv
    {f₀ f₁ : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf₀ : ∀ x : X, f₀ x ∈ e.baseSet)
    (hf₁ : ∀ x : X, f₁ x ∈ e.baseSet)
    (x : X) :
    ((⇑f₀ *ᵖ E) x) ≃L[ℝ] ((⇑f₁ *ᵖ E) x) :=
  -- The endpoint transport is the forward chart map at `f₀ x` followed by the inverse chart map
  -- at `f₁ x`, both evaluated in the same global trivialization.
  (pullbackTrivializationContinuousLinearEquiv
      e x (hf₀ x)).trans
    ((pullbackTrivializationContinuousLinearEquiv
      e x (hf₁ x)).symm)

/-- Helper for Proposition 23.1.3: one global linear trivialization over the whole homotopy image
already determines an isomorphism between the two endpoint pullback bundles. -/
private lemma globalPullbackTransportContinuous
    {f₀ f₁ : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf₀ : ∀ x : X, f₀ x ∈ e.baseSet)
    (hf₁ : ∀ x : X, f₁ x ∈ e.baseSet) :
    Continuous fun z : Bundle.TotalSpace (Fin n → ℝ) (f₀ *ᵖ E) ↦
      @Bundle.TotalSpace.mk X (Fin n → ℝ) (f₁ *ᵖ E) z.1
        (((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₀ z.1)).trans
          ((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₁ z.1)).symm)) z.2) := by
  let homeomorph₀ := globalPullbackTrivializationHomeomorph e hf₀
  let homeomorph₁ := globalPullbackTrivializationHomeomorph e hf₁
  have hEq :
      (fun z : Bundle.TotalSpace (Fin n → ℝ) (f₀ *ᵖ E) ↦ homeomorph₁.symm (homeomorph₀ z)) =
        fun z : Bundle.TotalSpace (Fin n → ℝ) (f₀ *ᵖ E) ↦
          @Bundle.TotalSpace.mk X (Fin n → ℝ) (f₁ *ᵖ E) z.1
            (((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₀ z.1)).trans
              ((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₁ z.1)).symm)) z.2) := by
    -- The composite homeomorphism acts fiberwise by the expected transition
    -- `continuousLinearEquivAt₀.trans continuousLinearEquivAt₁.symm`.
    funext z
    simp [homeomorph₀, homeomorph₁, globalPullbackTrivializationHomeomorph_apply,
      globalPullbackTrivializationHomeomorph_symm_apply, pullbackTrivializationContinuousLinearEquiv,
      pullbackTrivializationContinuousLinearEquiv_apply,
      pullbackTrivializationContinuousLinearEquiv_symm_apply]
  -- The forward total-space transport is exactly the composition of the two chart homeomorphisms.
  rw [← hEq]
  exact homeomorph₁.continuous_invFun.comp homeomorph₀.continuous_toFun

/-- Helper for Proposition 23.1.3: the inverse global transport is continuous for the same chart
reason, with the endpoint roles reversed. -/
private lemma globalPullbackTransportContinuousSymm
    {f₀ f₁ : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf₀ : ∀ x : X, f₀ x ∈ e.baseSet)
    (hf₁ : ∀ x : X, f₁ x ∈ e.baseSet) :
    Continuous fun z : Bundle.TotalSpace (Fin n → ℝ) (f₁ *ᵖ E) ↦
      @Bundle.TotalSpace.mk X (Fin n → ℝ) (f₀ *ᵖ E) z.1
        (((((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₀ z.1)).trans
          ((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₁ z.1)).symm)).symm) z.2)) := by
  let homeomorph₀ := globalPullbackTrivializationHomeomorph e hf₀
  let homeomorph₁ := globalPullbackTrivializationHomeomorph e hf₁
  have hEq :
      (fun z : Bundle.TotalSpace (Fin n → ℝ) (f₁ *ᵖ E) ↦ homeomorph₀.symm (homeomorph₁ z)) =
        fun z : Bundle.TotalSpace (Fin n → ℝ) (f₁ *ᵖ E) ↦
          @Bundle.TotalSpace.mk X (Fin n → ℝ) (f₀ *ᵖ E) z.1
            (((((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₀ z.1)).trans
              ((pullbackTrivializationContinuousLinearEquiv e z.1 (hf₁ z.1)).symm)).symm) z.2)) := by
    -- The reverse composite homeomorphism carries the inverse fiber map.
    funext z
    simp [homeomorph₀, homeomorph₁, globalPullbackTrivializationHomeomorph_apply,
      globalPullbackTrivializationHomeomorph_symm_apply, pullbackTrivializationContinuousLinearEquiv,
      pullbackTrivializationContinuousLinearEquiv_apply,
      pullbackTrivializationContinuousLinearEquiv_symm_apply]
  -- The inverse total-space transport is the opposite composition of the same two chart
  -- homeomorphisms.
  rw [← hEq]
  exact homeomorph₀.continuous_invFun.comp homeomorph₁.continuous_toFun

/-- Helper for Proposition 23.1.3: one global linear trivialization over the whole homotopy image
already determines an isomorphism between the two endpoint pullback bundles. -/
private noncomputable def realPlaneBundleIsoOfGlobalPullbackTrivializations
    {f₀ f₁ : ContinuousMap X B}
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hf₀ : ∀ x : X, f₀ x ∈ e.baseSet)
    (hf₁ : ∀ x : X, f₁ x ∈ e.baseSet) :
    PullbackRealPlaneBundleIso n E f₀ f₁ :=
  -- The chart transport gives the fiberwise linear equivalence, and the total-space continuity
  -- has already been normalized above through the global chart homeomorphisms.
  -- Local instance justification (typeclass): the `PullbackRealPlaneBundleIso` owner uses the
  -- coercion-shaped pullback module family, and the structure literal needs those instances
  -- available while elaborating its fiberwise `ContinuousLinearEquiv` field.
  letI : ∀ x : X, Module ℝ ((⇑f₀ *ᵖ E) x) := continuousMapCoePullbackModules f₀ E
  -- Local instance justification (typeclass): the target pullback family needs the same
  -- coercion-shaped module bridge for the inverse fiber transport field.
  letI : ∀ x : X, Module ℝ ((⇑f₁ *ᵖ E) x) := continuousMapCoePullbackModules f₁ E
  @RealPlaneBundleIso.mk n X _ (f₀ *ᵖ E) (f₁ *ᵖ E) _ _ _ _
    (fun x ↦ continuousMapPullbackAddCommGroup f₀ E x)
    (fun x ↦ continuousMapPullbackAddCommGroup f₁ E x)
    (continuousMapCoePullbackModules f₀ E)
    (continuousMapCoePullbackModules f₁ E)
    (fun x ↦ globalPullbackFiberLinearEquiv e hf₀ hf₁ x)
    (globalPullbackTransportContinuous e hf₀ hf₁)
    (globalPullbackTransportContinuousSymm e hf₀ hf₁)

/-- If one trivialization contains the whole homotopy image, then the two endpoint pullbacks are
already globally isomorphic. -/
private theorem pullbackRealPlaneBundleIsoOfGlobalTrivialization
    {f₀ f₁ : ContinuousMap X B} (H : ContinuousMap.Homotopy f₀ f₁)
    (e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ]
    (hmem : ∀ p : unitInterval × X, H p ∈ e.baseSet) :
    Nonempty (PullbackRealPlaneBundleIso n E f₀ f₁) := by
  have hf₀ : ∀ x : X, f₀ x ∈ e.baseSet := fun x ↦ by
    -- Evaluating the homotopy at time `0` places the first endpoint inside the chart.
    simpa [H.apply_zero x] using hmem (0, x)
  have hf₁ : ∀ x : X, f₁ x ∈ e.baseSet := fun x ↦ by
    -- Evaluating the homotopy at time `1` places the second endpoint inside the chart.
    simpa [H.apply_one x] using hmem (1, x)
  -- Route correction: package the endpoint transport through the global chart-induced
  -- homeomorphisms, rather than constructing the continuity fields directly inside the owner.
  exact ⟨realPlaneBundleIsoOfGlobalPullbackTrivializations e hf₀ hf₁⟩

/-- Helper for Proposition 23.1.3: around each homotopy point `(t₀, x₀)`, one fixed
trivialization is valid on a product neighborhood in `unitInterval × X`. -/
private lemma existsTrivializationNeighborhoodAtHomotopyPoint
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁) (p₀ : unitInterval × X) :
    ∃ s : Set unitInterval, ∃ U : Set X,
      IsOpen s ∧ p₀.1 ∈ s ∧ IsOpen U ∧ p₀.2 ∈ U ∧
      ∃ e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E),
        Trivialization.IsLinear ℝ e ∧
        ∀ ⦃t : unitInterval⦄ ⦃x : X⦄, t ∈ s → x ∈ U → H (t, x) ∈ e.baseSet := by
  let e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E) :=
    trivializationAt (Fin n → ℝ) E (H p₀)
  have heLinear : Trivialization.IsLinear ℝ e := by
    -- The preferred vector-bundle trivialization is fiberwise linear by the ambient bundle
    -- structure.
    dsimp [e]
    infer_instance
  have hp₀ : H p₀ ∈ e.baseSet := by
    -- The trivialization centered at `H p₀` contains that base point by construction.
    simpa [e] using mem_baseSet_trivializationAt (Fin n → ℝ) E (H p₀)
  have hpre : H ⁻¹' e.baseSet ∈ nhds p₀ := by
    -- Pulling back the open base set along the homotopy gives a neighborhood of `(t₀, x₀)`.
    have hHcont : Continuous H := H.continuous
    have hHcontAt : ContinuousAt H p₀ := hHcont.continuousAt
    exact hHcontAt.preimage_mem_nhds (IsOpen.mem_nhds e.open_baseSet hp₀)
  rcases mem_nhds_prod_iff'.1 hpre with ⟨s, U, hsOpen, hp₀s, hUOpen, hp₀U, hsub⟩
  refine ⟨s, U, hsOpen, hp₀s, hUOpen, hp₀U, e, heLinear, ?_⟩
  intro t x ht hx
  -- Membership in the chosen product neighborhood forces the homotopy value into `e.baseSet`.
  exact hsub ⟨ht, hx⟩

/-- Helper for Proposition 23.1.3: for each `x₀ : X`, compactness of `unitInterval` upgrades the
pointwise product-neighborhood charts to finitely many time neighborhoods sharing one open base
neighborhood of `x₀`. -/
private lemma existsFiniteTrivializationNeighborhoodCover
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁) (x₀ : X) :
    ∃ (T : Finset unitInterval) (s : unitInterval → Set unitInterval)
      (U : Set X)
      (e : unitInterval →
        Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E)),
      (∀ t ∈ T, Trivialization.IsLinear ℝ (e t)) ∧
      (∀ t : unitInterval, IsOpen (s t)) ∧
      Set.univ ⊆ ⋃ t ∈ T, s t ∧
      IsOpen U ∧ x₀ ∈ U ∧
      ∀ t ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄, τ ∈ s t → x ∈ U → H (τ, x) ∈ (e t).baseSet := by
  classical
  have hpoint :
      ∀ t : unitInterval,
        ∃ s : Set unitInterval, ∃ U : Set X,
          IsOpen s ∧ t ∈ s ∧ IsOpen U ∧ x₀ ∈ U ∧
          ∃ e : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E),
            Trivialization.IsLinear ℝ e ∧
            ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄, τ ∈ s → x ∈ U → H (τ, x) ∈ e.baseSet := by
    intro t
    exact existsTrivializationNeighborhoodAtHomotopyPoint H (t, x₀)
  choose s V hsOpen hsMem hVOpen hxMem e heLinear hchart using hpoint
  have hcoverAll : Set.univ ⊆ ⋃ t : unitInterval, s t := by
    intro t _
    exact Set.mem_iUnion.2 ⟨t, hsMem t⟩
  obtain ⟨T, hTcover⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set unitInterval)).elim_finite_subcover
      s hsOpen hcoverAll
  let U : Set X := ⋂ t ∈ T, V t
  have hUOpen : IsOpen U := by
    -- The common base neighborhood is a finite intersection of the individual neighborhoods.
    simpa [U] using isOpen_biInter_finset fun t _ ↦ hVOpen t
  have hx₀U : x₀ ∈ U := by
    -- Each local neighborhood contains `x₀`, so their finite intersection does as well.
    simp [U, hxMem]
  refine ⟨T, s, U, e, (fun t ht ↦ heLinear t), hsOpen, hTcover, hUOpen, hx₀U, ?_⟩
  intro t ht τ x hτ hx
  have hxAll : ∀ t ∈ T, x ∈ V t := by
    simpa [U] using hx
  have hxV : x ∈ V t := by
    -- Membership in the common neighborhood specializes to the `t`-th local neighborhood.
    exact hxAll t ht
  exact hchart t hτ hxV

/-- Helper for Proposition 23.1.3: a finite open cover of `unitInterval` refines to a monotone
chain of knots whose adjacent strips lie in chosen cover members. -/
private lemma finiteMonotoneStripDataOfNeighborhoodCover
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval}
    (hsOpen : ∀ t : unitInterval, IsOpen (s t))
    (hcover : Set.univ ⊆ ⋃ t ∈ T, s t) :
    ∃ t : ℕ → unitInterval, t 0 = 0 ∧ Monotone t ∧
      (∃ nMax : ℕ, ∀ m ≥ nMax, t m = 1) ∧
      ∀ n : ℕ, ∃ i : ↑T, Set.Icc (t n) (t (n + 1)) ⊆ s i := by
  have hcover' : Set.univ ⊆ ⋃ i : ↑T, s i := by
    intro x hx
    rcases Set.mem_iUnion.1 (hcover hx) with ⟨i, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨hi, hxi⟩
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩
  -- This is exactly mathlib's monotone-partition theorem, specialized to the chosen finite cover.
  simpa using
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i : ↑T ↦ hsOpen i)
      hcover'

/-- Helper for Proposition 23.1.3: the time-`τ` slice of a homotopy restricts to any base subset
`U`. -/
private def homotopySliceOn
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁) (U : Set X) (τ : unitInterval) :
    ContinuousMap ↥U B :=
  ⟨fun y ↦ H (τ, y.1), H.continuous.comp (continuous_const.prodMk continuous_subtype_val)⟩

/-- Helper for Proposition 23.1.3: freeze the owner for pullback-bundle isomorphisms over the
subtype base `↥U`, so stripwise recursion does not have to re-elaborate the coercion-shaped
pullback module instances. -/
private abbrev subtypePullbackIso
    (U : Set X) (g₀ g₁ : ContinuousMap ↥U B) : Type _ :=
  @PullbackRealPlaneBundleIso n ↥U inferInstance B inferInstance E
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    g₀
    g₁

/-- Helper for Proposition 23.1.3: the restricted pullback bundle is canonically isomorphic to
itself. -/
private def subtypePullbackIsoRefl
    (U : Set X) (g : ContinuousMap ↥U B) :
    PullbackRealPlaneBundleIso n E g g :=
  -- Route correction: build the frozen owner directly, so no instance search remains on the
  -- coercion-shaped pullback family.
  @RealPlaneBundleIso.mk n ↥U inferInstance ((⇑g) *ᵖ E) ((⇑g) *ᵖ E) _ _ _ _
    (fun x ↦ continuousMapPullbackAddCommGroup g E x)
    (fun x ↦ continuousMapPullbackAddCommGroup g E x)
    (continuousMapCoePullbackModules g E)
    (continuousMapCoePullbackModules g E)
    (fun x ↦ ContinuousLinearEquiv.refl ℝ (((⇑g) *ᵖ E) x))
    continuous_id
    continuous_id

/-- Helper for Proposition 23.1.3: the left endpoint of each monotone strip lies in the strip's
chosen chart neighborhood. -/
private lemma stripLeftEndpoint_mem
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval}
    (t : ℕ → unitInterval) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (k : ℕ) :
    t k ∈ s (label k) := by
  -- Monotonicity puts the left knot in the closed interval controlled by the `k`-th chart.
  exact hsub k (Set.left_mem_Icc.2 (htmono (Nat.le_succ k)))

/-- Helper for Proposition 23.1.3: the right endpoint of each monotone strip lies in the same
chosen chart neighborhood. -/
private lemma stripRightEndpoint_mem
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval}
    (t : ℕ → unitInterval) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (k : ℕ) :
    t (k + 1) ∈ s (label k) := by
  -- The right knot lies in the same interval, so the chosen strip chart also contains it.
  exact hsub k (Set.right_mem_Icc.2 (htmono (Nat.le_succ k)))

/-- Helper for Proposition 23.1.3: one strip in the monotone time subdivision yields a local
endpoint pullback-bundle isomorphism over `↥U`. -/
private noncomputable def stripStepPullbackIsoOn
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    (k : ℕ) :
    PullbackRealPlaneBundleIso n E
      (homotopySliceOn H U (t k))
      (homotopySliceOn H U (t (k + 1))) :=
  -- Local instance justification (typeclass): `realPlaneBundleIsoOfGlobalPullbackTrivializations`
  -- records linearity as an instance on the chosen trivialization.
  letI : Trivialization.IsLinear ℝ (e (label k)) := hlinear (label k) (label k).2
  -- Route correction: specialize the already-global chart-transport construction to the subtype
  -- base `↥U` instead of composing at the `PullbackRealPlaneBundleIso` abbreviation surface.
  realPlaneBundleIsoOfGlobalPullbackTrivializations
    (e (label k))
    (fun y ↦
      hchart (label k) (label k).2
        (stripLeftEndpoint_mem t htmono label hsub k)
        y.2)
    (fun y ↦
      hchart (label k) (label k).2
        (stripRightEndpoint_mem t htmono label hsub k)
        y.2)

/-- Helper for Proposition 23.1.3: recursively composing the stripwise transports reaches every
knot value in the monotone subdivision. -/
private noncomputable def localPullbackIsoToKnot
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet) :
    ∀ m : ℕ,
      PullbackRealPlaneBundleIso n E
        (homotopySliceOn H U (t 0))
        (homotopySliceOn H U (t m))
    | 0 =>
        -- The recursion starts at the first knot and so begins with the identity transport.
        subtypePullbackIsoRefl U (homotopySliceOn H U (t 0))
    | m + 1 =>
        -- Route correction: compose inside one fixed spelling world for the three knot slices,
        -- instead of routing through a standalone subtype composition helper.
        let g₀ := homotopySliceOn H U (t 0)
        let gₘ := homotopySliceOn H U (t m)
        let gₘ₁ := homotopySliceOn H U (t (m + 1))
        -- Local instance justification (proof-local temporary data): the recursive branch uses the `g₀` pullback fiber group only to type the composed transport term below.
        letI : ∀ x : ↥U, AddCommGroup ((⇑g₀ *ᵖ E) x) := fun x ↦ continuousMapPullbackAddCommGroup g₀ E x
        -- Local instance justification (proof-local temporary data): the midpoint slice group instance is introduced only to form the intermediate recursive composition target.
        letI : ∀ x : ↥U, AddCommGroup ((⇑gₘ *ᵖ E) x) := fun x ↦ continuousMapPullbackAddCommGroup gₘ E x
        -- Local instance justification (proof-local temporary data): the successor slice group instance is needed only for the endpoint of this local composition step.
        letI : ∀ x : ↥U, AddCommGroup ((⇑gₘ₁ *ᵖ E) x) := fun x ↦ continuousMapPullbackAddCommGroup gₘ₁ E x
        letI : ∀ x : ↥U, Module ℝ ((⇑g₀ *ᵖ E) x) := continuousMapCoePullbackModules g₀ E
        letI : ∀ x : ↥U, Module ℝ ((⇑gₘ *ᵖ E) x) := continuousMapCoePullbackModules gₘ E
        letI : ∀ x : ↥U, Module ℝ ((⇑gₘ₁ *ᵖ E) x) := continuousMapCoePullbackModules gₘ₁ E
        let η₀m : PullbackRealPlaneBundleIso n E g₀ gₘ :=
          localPullbackIsoToKnot H e hlinear t ht0 htmono label hsub hchart m
        let ηmSucc : PullbackRealPlaneBundleIso n E gₘ gₘ₁ :=
          stripStepPullbackIsoOn H e hlinear t htmono label hsub hchart m
        @realPlaneBundleIsoTrans
          ↥U
          inferInstance
          n
          ((⇑g₀) *ᵖ E)
          ((⇑gₘ) *ᵖ E)
          ((⇑gₘ₁) *ᵖ E)
          inferInstance
          inferInstance
          inferInstance
          inferInstance
          inferInstance
          inferInstance
          (fun x ↦ continuousMapPullbackAddCommGroup g₀ E x)
          (fun x ↦ continuousMapPullbackAddCommGroup gₘ E x)
          (fun x ↦ continuousMapPullbackAddCommGroup gₘ₁ E x)
          (continuousMapCoePullbackModules g₀ E)
          (continuousMapCoePullbackModules gₘ E)
          (continuousMapCoePullbackModules gₘ₁ E)
          η₀m
          ηmSucc

/-- Helper for Proposition 23.1.3: ordered strip data on a neighborhood `U` yields a local bundle
isomorphism between the endpoint pullbacks over `↥U`. -/
private theorem localPullbackIsoOfFiniteMonotoneStripData
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (nMax : ℕ) (htMax : ∀ m ≥ nMax, t m = 1)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet) :
    Nonempty
      (PullbackRealPlaneBundleIso n E
        (homotopySliceOn H U 0)
        (homotopySliceOn H U 1)) := by
  have η :=
    localPullbackIsoToKnot
      H e hlinear t ht0 htmono label hsub hchart
      nMax
  have h1 : t nMax = 1 := htMax nMax le_rfl
  have hstart : homotopySliceOn H U (t 0) = homotopySliceOn H U 0 := by
    -- The recursive start knot is the actual initial endpoint after rewriting `t 0 = 0`.
    ext y
    rw [ht0]
  have hend : homotopySliceOn H U (t nMax) = homotopySliceOn H U 1 := by
    -- The eventual-constancy hypothesis identifies the terminal knot with time `1`.
    ext y
    rw [h1]
  have η' :
      PullbackRealPlaneBundleIso n E
        (homotopySliceOn H U 0)
        (homotopySliceOn H U 1) := by
    simpa [hstart, hend] using η
  exact ⟨η'⟩

/-- Helper for Proposition 23.1.3: each base point admits an open neighborhood together with the
explicit finite strip data used to construct the local endpoint pullback isomorphism. -/
private theorem localStripWitnessNeighborhood
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁) (x₀ : X) :
    ∃ (U : Set X)
      (T : Finset unitInterval)
      (s : unitInterval → Set unitInterval)
      (e : unitInterval →
        Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
      (t : ℕ → unitInterval)
      (nMax : ℕ)
      (label : ℕ → ↑T),
      IsOpen U ∧
      x₀ ∈ U ∧
      (∀ i ∈ T, Trivialization.IsLinear ℝ (e i)) ∧
      (∀ i : unitInterval, IsOpen (s i)) ∧
      t 0 = 0 ∧
      Monotone t ∧
      (∀ m ≥ nMax, t m = 1) ∧
      (∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k)) ∧
      (∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
        τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet) := by
  have hfinite :
      ∃ (T : Finset unitInterval) (s : unitInterval → Set unitInterval)
        (U : Set X)
        (e : unitInterval →
          Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E)),
        (∀ t ∈ T, Trivialization.IsLinear ℝ (e t)) ∧
        (∀ t : unitInterval, IsOpen (s t)) ∧
        Set.univ ⊆ ⋃ t ∈ T, s t ∧
        IsOpen U ∧ x₀ ∈ U ∧
        ∀ t ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄, τ ∈ s t → x ∈ U → H (τ, x) ∈ (e t).baseSet :=
    existsFiniteTrivializationNeighborhoodCover H x₀
  rcases hfinite with
    ⟨T, s, U, e, hlinear, hsOpen, hTcover, hUOpen, hx₀U, hchart⟩
  rcases finiteMonotoneStripDataOfNeighborhoodCover hsOpen hTcover with
    ⟨t, ht0, htmono, ⟨nMax, htMax⟩, hsub⟩
  choose label hlabel using hsub
  -- Keep the actual strip data visible so later overlap arguments can compare two witnesses
  -- pointwise instead of unpacking an opaque `Nonempty` local bundle isomorphism.
  refine ⟨U, T, s, e, t, nMax, label, hUOpen, hx₀U, hlinear, hsOpen, ht0, htmono, ?_, ?_, ?_⟩
  · exact htMax
  · exact hlabel
  · exact hchart

/-- Helper for Proposition 23.1.3: every base point has an open neighborhood on which the
endpoint pullbacks of the homotopy are already bundle-isomorphic. -/
private theorem localPullbackIsoNeighborhood
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁) (x₀ : X) :
    ∃ U : Set X,
      IsOpen U ∧ x₀ ∈ U ∧
      Nonempty
        (PullbackRealPlaneBundleIso n E
          (homotopySliceOn H U 0)
          (homotopySliceOn H U 1)) := by
  have hwitness :
      ∃ (U : Set X)
        (T : Finset unitInterval)
        (s : unitInterval → Set unitInterval)
        (e : unitInterval →
          Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
        (t : ℕ → unitInterval)
        (nMax : ℕ)
        (label : ℕ → ↑T),
        IsOpen U ∧
        x₀ ∈ U ∧
        (∀ i ∈ T, Trivialization.IsLinear ℝ (e i)) ∧
        (∀ i : unitInterval, IsOpen (s i)) ∧
        t 0 = 0 ∧
        Monotone t ∧
        (∀ m ≥ nMax, t m = 1) ∧
        (∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k)) ∧
        (∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
          τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet) :=
    localStripWitnessNeighborhood H x₀
  rcases hwitness with
    ⟨U, T, s, e, t, nMax, label, hUOpen, hx₀U, hlinear, _, ht0, htmono, htMax, hsub, hchart⟩
  refine ⟨U, hUOpen, hx₀U, ?_⟩
  -- The finite monotone strip data closes the local homotopy transport on the chosen
  -- neighborhood.
  exact localPullbackIsoOfFiniteMonotoneStripData
    H e hlinear t ht0 htmono nMax htMax label hsub
    hchart

/-- Helper for Proposition 23.1.3: pullback chart changes are exactly the original chart changes
evaluated after the base map. -/
private lemma pullbackCoordChangeL_eq
    {Y : Type*} [TopologicalSpace Y]
    (g : ContinuousMap Y B)
    (e e' : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e.IsLinear ℝ] [e'.IsLinear ℝ]
    {y : Y} (hy : g y ∈ e.baseSet ∩ e'.baseSet) :
    (e.pullback g).coordChangeL ℝ (e'.pullback g) y =
      e.coordChangeL ℝ e' (g y) := by
  -- Route correction: normalize pullback overlap maps once, then keep all later transport
  -- comparisons in the base-space `coordChangeL` spelling.
  ext v i
  have hy' : y ∈ (e.pullback g).baseSet ∩ (e'.pullback g).baseSet := by
    simpa using hy
  exact congrFun
    (by
      rw [e.coordChangeL_apply e' hy]
      rw [(e.pullback g).coordChangeL_apply' (e'.pullback g) hy' v]
      rfl)
    i

/-- Helper for Proposition 23.1.3: the boundary transport between adjacent pullback charts is the
base-space coordinate change at the knot value. -/
private lemma adjacentStripBoundaryTransport_eq_coordChangeL
    {Y : Type*} [TopologicalSpace Y]
    (g : ContinuousMap Y B)
    (e₀ e₁ : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e₀.IsLinear ℝ] [e₁.IsLinear ℝ]
    (y : Y) (h₀ : g y ∈ e₀.baseSet) (h₁ : g y ∈ e₁.baseSet) :
    ((pullbackTrivializationContinuousLinearEquiv e₀ y h₀).symm.trans
        (pullbackTrivializationContinuousLinearEquiv e₁ y h₁)) =
      e₀.coordChangeL ℝ e₁ (g y) := by
  have hy : y ∈ (e₀.pullback g).baseSet ∩ (e₁.pullback g).baseSet := by
    simpa using (show g y ∈ e₀.baseSet ∩ e₁.baseSet from ⟨h₀, h₁⟩)
  -- The adjacent transport is first the pullback chart change, then the pullback/base
  -- normalization lemma removes the remaining spelling mismatch.
  calc
    ((pullbackTrivializationContinuousLinearEquiv e₀ y h₀).symm.trans
        (pullbackTrivializationContinuousLinearEquiv e₁ y h₁)) =
        (e₀.pullback g).coordChangeL ℝ (e₁.pullback g) y := by
          simpa [pullbackTrivializationContinuousLinearEquiv] using
            (Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
              (e₀.pullback g) (e₁.pullback g) hy)
    _ = e₀.coordChangeL ℝ e₁ (g y) := pullbackCoordChangeL_eq g e₀ e₁ ⟨h₀, h₁⟩

/-- Helper for Proposition 23.1.3: coordinate changes satisfy the expected cocycle law on triple
overlaps. -/
private lemma coordChangeL_transOnTripleOverlap
    (e₀ e₁ e₂ : Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    [e₀.IsLinear ℝ] [e₁.IsLinear ℝ] [e₂.IsLinear ℝ]
    {b : B} (hb : b ∈ e₀.baseSet ∩ e₁.baseSet ∩ e₂.baseSet) :
    (e₀.coordChangeL ℝ e₁ b).trans (e₁.coordChangeL ℝ e₂ b) = e₀.coordChangeL ℝ e₂ b := by
  have hb01 : b ∈ e₀.baseSet ∩ e₁.baseSet := ⟨hb.1.1, hb.1.2⟩
  have hb12 : b ∈ e₁.baseSet ∩ e₂.baseSet := ⟨hb.1.2, hb.2⟩
  have hb02 : b ∈ e₀.baseSet ∩ e₂.baseSet := ⟨hb.1.1, hb.2⟩
  -- Rewrite each coordinate change into the chart-linear equivalences at the common base point,
  -- so the middle terms cancel by the linear-equivalence identities.
  apply ContinuousLinearEquiv.toLinearEquiv_injective
  rw [ContinuousLinearEquiv.trans_toLinearEquiv,
    Bundle.Trivialization.coe_coordChangeL' e₀ e₁ hb01,
    Bundle.Trivialization.coe_coordChangeL' e₁ e₂ hb12,
    Bundle.Trivialization.coe_coordChangeL' e₀ e₂ hb02]
  let A : E b ≃ₗ[ℝ] Fin n → ℝ := e₀.linearEquivAt ℝ b hb01.1
  let B : E b ≃ₗ[ℝ] Fin n → ℝ := e₁.linearEquivAt ℝ b hb01.2
  let C : E b ≃ₗ[ℝ] Fin n → ℝ := e₂.linearEquivAt ℝ b hb12.2
  change A.symm.trans (B.trans (B.symm.trans C)) = A.symm.trans C
  calc
    A.symm.trans (B.trans (B.symm.trans C))
        = A.symm.trans ((B.trans B.symm).trans C) := by
            rw [LinearEquiv.trans_assoc]
    _ = A.symm.trans ((LinearEquiv.refl ℝ (E b)).trans C) := by
          rw [LinearEquiv.self_trans_symm]
    _ = A.symm.trans C := by
          rw [LinearEquiv.refl_trans]

/-- Helper for Proposition 23.1.3: specializing one local strip witness at a fixed base point
turns strip-interval membership into chart membership along the path `τ ↦ H (τ, x)`. -/
private lemma pointwiseChartMem_ofLocalWitness
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    {t : ℕ → unitInterval} {label : ℕ → ↑T}
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) {k : ℕ} {τ : unitInterval}
    (hτ : τ ∈ Set.Icc (t k) (t (k + 1))) :
    H (τ, x) ∈ (e (label k)).baseSet := by
  -- Specializing the neighborhood witness at `x` removes the open-set parameter from the later
  -- fixed-point overlap comparison.
  exact hchart (label k) (label k).2 (hsub k hτ) hx

/-- Helper for Proposition 23.1.3: evaluating the recursive local strip transport at one base
point produces the corresponding fiber transport to the `m`-th knot. -/
private noncomputable def localWitnessFiberEquivToKnot
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) (m : ℕ) :=
  let g₀ := homotopySliceOn H U (t 0)
  let gₘ := homotopySliceOn H U (t m)
  -- Evaluate the recursive local bundle isomorphism at the fixed base point `⟨x, hx⟩`, keeping
  -- the coercion-shaped pullback modules explicit so no subtype-fiber instance search remains.
  @RealPlaneBundleIso.toContinuousLinearEquiv n ↥U inferInstance ((⇑g₀) *ᵖ E) ((⇑gₘ) *ᵖ E)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (fun y ↦ continuousMapPullbackAddCommGroup g₀ E y)
    (fun y ↦ continuousMapPullbackAddCommGroup gₘ E y)
    (continuousMapCoePullbackModules g₀ E)
    (continuousMapCoePullbackModules gₘ E)
    (localPullbackIsoToKnot H e hlinear t ht0 htmono label hsub hchart m)
    ⟨x, hx⟩

/-- Helper for Proposition 23.1.3: after specializing to one `x`, the overlap between adjacent
strip charts is exactly the base-space coordinate change at the shared knot value. -/
private noncomputable def localWitnessChartFiberEquiv
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    (j : ℕ) {τ : unitInterval} (hτ : τ ∈ Set.Icc (t j) (t (j + 1)))
    {x : X} (hx : x ∈ U) :
    ((⇑(homotopySliceOn H U τ) *ᵖ E) ⟨x, hx⟩) ≃L[ℝ] (Fin n → ℝ) :=
  let g := homotopySliceOn H U τ
  -- The chosen strip chart contributes one concrete chart map on the fiber over `(τ, x)`.
  letI : Trivialization.IsLinear ℝ (e (label j)) := hlinear (label j) (label j).2
  have hmem : g ⟨x, hx⟩ ∈ (e (label j)).baseSet :=
    pointwiseChartMem_ofLocalWitness H e hsub hchart hx hτ
  @Bundle.Trivialization.continuousLinearEquivAt
    ℝ
    ↥U
    (Fin n → ℝ)
    (⇑g *ᵖ E)
    inferInstance
    inferInstance
    (continuousMapCoePullbackModules g E)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    ((e (label j)).pullback g)
    inferInstance
    ⟨x, hx⟩
    hmem

/-- Helper for Proposition 23.1.3: after specializing to one `x`, the overlap between adjacent
strip charts is exactly the base-space coordinate change at the shared knot value. -/
private noncomputable def localWitnessCoordChangeAtSharedKnot
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval)
    (label : ℕ → ↑T)
    (k : ℕ) (x : X) :=
  letI : Trivialization.IsLinear ℝ (e (label k)) := hlinear (label k) (label k).2
  letI : Trivialization.IsLinear ℝ (e (label (k + 1))) := hlinear (label (k + 1)) (label (k + 1)).2
  (e (label k)).coordChangeL ℝ (e (label (k + 1))) (H (t (k + 1), x))

/-- Helper for Proposition 23.1.3: after specializing to one `x`, the overlap between adjacent
strip charts is exactly the base-space coordinate change at the shared knot value. -/
private lemma localWitnessBoundaryTransport_eq_coordChangeL
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) (k : ℕ) :
    ContinuousLinearEquiv.trans
        ((localWitnessChartFiberEquiv
            H e hlinear t label hsub hchart
            k
            (Set.right_mem_Icc.2 (htmono (Nat.le_succ k)))
            hx).symm)
        (localWitnessChartFiberEquiv
          H e hlinear t label hsub hchart
        (k + 1)
        (Set.left_mem_Icc.2 (htmono (Nat.le_succ (k + 1))))
        hx) =
      localWitnessCoordChangeAtSharedKnot
        H e hlinear t label k x := by
  -- Equip the two adjacent charts with their linear structures before comparing the boundary
  -- transport with the base-space coordinate change.
  letI : Trivialization.IsLinear ℝ (e (label k)) := hlinear (label k) (label k).2
  letI : Trivialization.IsLinear ℝ (e (label (k + 1))) := hlinear (label (k + 1)) (label (k + 1)).2
  -- Both specialized pullback charts are taken at the shared knot `t (k + 1)`, so the generic
  -- adjacent-boundary normalization lemma applies directly.
  simpa [localWitnessChartFiberEquiv, localWitnessCoordChangeAtSharedKnot] using
    (adjacentStripBoundaryTransport_eq_coordChangeL
      (homotopySliceOn H U (t (k + 1)))
      (e (label k))
      (e (label (k + 1)))
      ⟨x, hx⟩
      (pointwiseChartMem_ofLocalWitness H e hsub hchart hx
        (Set.right_mem_Icc.2 (htmono (Nat.le_succ k))))
      (pointwiseChartMem_ofLocalWitness H e hsub hchart hx
        (Set.left_mem_Icc.2 (htmono (Nat.le_succ (k + 1))))))

/-- Helper for Proposition 23.1.3: after fixing `x`, one strip contributes a concrete fiber map
from the `m`-th knot to the `(m + 1)`-st knot. -/
private noncomputable def localWitnessStripStepFiberEquiv
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) (m : ℕ) :=
  let gₘ := homotopySliceOn H U (t m)
  let gₘ₁ := homotopySliceOn H U (t (m + 1))
  -- Evaluate the `m`-th stripwise bundle isomorphism at the frozen base point `⟨x, hx⟩`.
  @RealPlaneBundleIso.toContinuousLinearEquiv n ↥U inferInstance ((⇑gₘ) *ᵖ E) ((⇑gₘ₁) *ᵖ E)
    inferInstance
    inferInstance
    inferInstance
    inferInstance
    (fun y ↦ continuousMapPullbackAddCommGroup gₘ E y)
    (fun y ↦ continuousMapPullbackAddCommGroup gₘ₁ E y)
    (continuousMapCoePullbackModules gₘ E)
    (continuousMapCoePullbackModules gₘ₁ E)
    (stripStepPullbackIsoOn
      H e hlinear t htmono label hsub hchart
      m)
    ⟨x, hx⟩

/-- Helper for Proposition 23.1.3: the specialized strip step is exactly the chart map at the
left endpoint followed by the inverse chart map at the right endpoint. -/
private lemma localWitnessStripStepFiberEquiv_eq_chart
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) (m : ℕ) :
    localWitnessStripStepFiberEquiv
        H e hlinear t htmono label hsub hchart
        hx
        m =
      ContinuousLinearEquiv.trans
        (localWitnessChartFiberEquiv
          H e hlinear t label hsub hchart
          m
          (Set.left_mem_Icc.2 (htmono (Nat.le_succ m)))
          hx)
        ((localWitnessChartFiberEquiv
          H e hlinear t label hsub hchart
          m
          (Set.right_mem_Icc.2 (htmono (Nat.le_succ m)))
          hx).symm) := by
  -- Unfold one strip transport: it is exactly the chart at the left endpoint followed by the
  -- inverse chart at the right endpoint inside the single chosen trivialization.
  rfl

/-- Helper for Proposition 23.1.3: the recursive endpoint transport after `m + 1` strips is the
pointwise `m`-strip transport followed by the specialized `(m + 1)`-st strip step. -/
private noncomputable def localWitnessFiberEquivToKnotSuccComposite
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) (m : ℕ) :
    ((⇑(homotopySliceOn H U (t 0)) *ᵖ E) ⟨x, hx⟩) ≃L[ℝ]
      ((⇑(homotopySliceOn H U (t (m + 1))) *ᵖ E) ⟨x, hx⟩) :=
  let g₀ := homotopySliceOn H U (t 0)
  let gₘ := homotopySliceOn H U (t m)
  let gₘ₁ := homotopySliceOn H U (t (m + 1))
  -- Keep the three slice-module instances explicit so the pointwise recursive transport stays in
  -- one elaboration spelling world.
  letI : ∀ y : ↥U, Module ℝ ((⇑g₀ *ᵖ E) y) := continuousMapCoePullbackModules g₀ E
  letI : ∀ y : ↥U, Module ℝ ((⇑gₘ *ᵖ E) y) := continuousMapCoePullbackModules gₘ E
  letI : ∀ y : ↥U, Module ℝ ((⇑gₘ₁ *ᵖ E) y) := continuousMapCoePullbackModules gₘ₁ E
  let η₀m :
      ((⇑g₀ *ᵖ E) ⟨x, hx⟩) ≃L[ℝ] ((⇑gₘ *ᵖ E) ⟨x, hx⟩) :=
    localWitnessFiberEquivToKnot
      H e hlinear t ht0 htmono label hsub hchart
      hx
      m
  let ηmSucc :
      ((⇑gₘ *ᵖ E) ⟨x, hx⟩) ≃L[ℝ] ((⇑gₘ₁ *ᵖ E) ⟨x, hx⟩) :=
    localWitnessStripStepFiberEquiv
      H e hlinear t htmono label hsub hchart
      hx
      m
  η₀m.trans ηmSucc

/-- Helper for Proposition 23.1.3: the recursive pointwise transport advances by composing with
the next strip step. -/
private lemma localWitnessFiberEquivToKnot_succ
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) (m : ℕ) :
    localWitnessFiberEquivToKnot
        H e hlinear t ht0 htmono label hsub hchart
        hx
        (m + 1) =
      localWitnessFiberEquivToKnotSuccComposite
        H e hlinear t ht0 htmono label hsub hchart
        hx
        m := by
  -- Unfold the recursive branch once; evaluating the composed bundle isomorphism at `x` is the
  -- explicit pointwise composite recorded in `localWitnessFiberEquivToKnotSuccComposite`.
  simp [localWitnessFiberEquivToKnot, localWitnessFiberEquivToKnotSuccComposite,
    localWitnessStripStepFiberEquiv, localPullbackIsoToKnot, realPlaneBundleIsoTrans]
  rfl

/-- Helper for Proposition 23.1.3: the recursive pointwise transport starts from the identity on
the initial knot. -/
private lemma localWitnessFiberEquivToKnot_zero
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) :
    localWitnessFiberEquivToKnot
        H e hlinear t ht0 htmono label hsub hchart
        hx
        0 =
      ContinuousLinearEquiv.refl ℝ
        (((⇑(homotopySliceOn H U (t 0)) *ᵖ E) ⟨x, hx⟩)) := by
  -- Unfold the zeroth recursive branch: the local transport begins with the identity bundle
  -- isomorphism, so evaluating it at `x` gives the fiberwise identity.
  rfl

/-- Helper for Proposition 23.1.3: the terminal recursive knot transport has the same fiber type
as the endpoint map once `t 0 = 0` and `t nMax = 1` are imposed. -/
private lemma localWitnessInitialSlice_eq_zero
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {U : Set X}
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) :
    homotopySliceOn H U (t 0) = homotopySliceOn H U 0 := by
  -- Rewriting the initial knot identifies the recursive source slice with the time-`0` endpoint.
  ext y
  rw [ht0]

/-- Helper for Proposition 23.1.3: the terminal knot of one local witness is the time-`1`
endpoint slice. -/
private lemma localWitnessTerminalSlice_eq_one
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {U : Set X}
    (t : ℕ → unitInterval) {nMax : ℕ} (htMax : ∀ m ≥ nMax, t m = 1) :
    homotopySliceOn H U (t nMax) = homotopySliceOn H U 1 := by
  -- Eventual constancy at `1` identifies the recursive target slice with the endpoint slice.
  ext y
  rw [htMax nMax le_rfl]

/-- Helper for Proposition 23.1.3: the terminal recursive knot transport has the same fiber type
as the endpoint map once `t 0 = 0` and `t nMax = 1` are imposed. -/
private lemma localWitnessTerminalFiberEquiv_type
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (nMax : ℕ) (htMax : ∀ m ≥ nMax, t m = 1)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) :
    (((⇑(homotopySliceOn H U (t 0)) *ᵖ E) ⟨x, hx⟩) ≃L[ℝ]
      ((⇑(homotopySliceOn H U (t nMax)) *ᵖ E) ⟨x, hx⟩)) =
    (((⇑(homotopySliceOn H U 0) *ᵖ E) ⟨x, hx⟩) ≃L[ℝ]
      ((⇑(homotopySliceOn H U 1) *ᵖ E) ⟨x, hx⟩)) := by
  -- Rewriting the slice maps identifies the recursive endpoint fiber types with the actual
  -- endpoint pullback fiber types.
  change (E (H (t 0, x)) ≃L[ℝ] E (H (t nMax, x))) =
      (E (H (0, x)) ≃L[ℝ] E (H (1, x)))
  have h0 : H (t 0, x) = H (0, x) := by
    rw [ht0]
  have h1 : H (t nMax, x) = H (1, x) := by
    rw [htMax nMax le_rfl]
  rw [h0, h1]

/-- Helper for Proposition 23.1.3: the terminal recursive knot transport, transported to the
endpoint fiber types. -/
private noncomputable def localWitnessTerminalFiberEquiv
    {f₀ f₁ : ContinuousMap X B}
    (H : ContinuousMap.Homotopy f₀ f₁)
    {T : Finset unitInterval} {s : unitInterval → Set unitInterval} {U : Set X}
    (e : unitInterval →
      Trivialization (Fin n → ℝ) (@Bundle.TotalSpace.proj B (Fin n → ℝ) E))
    (hlinear : ∀ i ∈ T, Trivialization.IsLinear ℝ (e i))
    (t : ℕ → unitInterval) (ht0 : t 0 = 0) (htmono : Monotone t)
    (nMax : ℕ) (htMax : ∀ m ≥ nMax, t m = 1)
    (label : ℕ → ↑T)
    (hsub : ∀ k : ℕ, Set.Icc (t k) (t (k + 1)) ⊆ s (label k))
    (hchart : ∀ i ∈ T, ∀ ⦃τ : unitInterval⦄ ⦃x : X⦄,
      τ ∈ s i → x ∈ U → H (τ, x) ∈ (e i).baseSet)
    {x : X} (hx : x ∈ U) :
    ((⇑(homotopySliceOn H U 0) *ᵖ E) ⟨x, hx⟩) ≃L[ℝ]
      ((⇑(homotopySliceOn H U 1) *ᵖ E) ⟨x, hx⟩) :=
  cast
    (localWitnessTerminalFiberEquiv_type
      H e hlinear t ht0 htmono nMax htMax label hsub hchart hx)
    (localWitnessFiberEquivToKnot
      H e hlinear t ht0 htmono label hsub hchart hx nMax)

/-- Proposition 23.1.3

Pullbacks of a real `n`-plane bundle along homotopic maps are equivalent bundles.  As in May, the
bundle owner uses numerable coordinate charts, so no paracompactness hypothesis on the source is
needed. The equivalence is formalized as a bundle isomorphism over the common source base. -/
theorem pullbackRealPlaneBundleIsoOfHomotopic
    {f₀ f₁ : ContinuousMap X B}
    (h : ContinuousMap.Homotopic f₀ f₁) :
    Nonempty (PullbackRealPlaneBundleIso n E f₀ f₁) := sorry

end
