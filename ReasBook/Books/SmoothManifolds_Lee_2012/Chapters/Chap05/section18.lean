import Mathlib.Geometry.Manifold.ContMDiffMap
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.SmoothEmbedding

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_5_18 (from Chap05/Sec05_37) -/
open scoped Manifold ContDiff

universe uE uH uM uE' uH'

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ⊤ M]
variable {S : Set M}
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} [ChartedSpace H' S] [IsManifold J ⊤ S]
variable [BoundarylessManifold J S]

/-- Helper for Problem 5-18: the preferred linear identification `ℝ ≃ ℝ¹`. -/
noncomputable def real_to_r1_equiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  ((EuclideanSpace.equiv (Fin 1) ℝ).trans
    (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ)).symm

/-- Helper for Problem 5-18: the chosen map from `ℝ` into `ℝ¹`. -/
noncomputable def real_to_r1 : ℝ → EuclideanSpace ℝ (Fin 1) :=
  real_to_r1_equiv

/-- Helper for Problem 5-18: the unique coordinate of the preferred `ℝ¹` point recovers the
original scalar. -/
theorem real_to_r1_apply_zero (t : ℝ) :
    real_to_r1 t 0 = t := by
  -- The preferred identification is the inverse of the standard `ℝ¹ ≃ ℝ`.
  simp [real_to_r1, real_to_r1_equiv]

/-- Helper for Problem 5-18: once an intrinsically smooth scalar function on `S` extends smoothly
near a point and is nonzero there, the nonvanishing locus of the ambient extension gives an ambient
open neighborhood whose intersection with `S` stays inside the prescribed support patch. -/
lemma ambient_open_refinement_of_extended_cutoff
    {U : TopologicalSpace.Opens S} {p : S}
    (hExt : ∀ f : C^⊤⟮J, S; ℝ⟯, (f : S → ℝ).IsSmoothOn I 𝓘(ℝ))
    {φ : C^⊤⟮J, S; ℝ⟯} (hφp : φ p = 1) (hφsupport : tsupport (φ : S → ℝ) ⊆ U) :
    ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U := by
  -- Unpack the local ambient extension promised by `Function.IsSmoothOn` at the chosen base point.
  rcases (Function.isSmoothOn_iff_exists_local_extension (f := (φ : S → ℝ))).1 (hExt φ) p with
    ⟨W, hW_open, hpW, Fext, hFext_smooth, hFext_eq⟩
  have hFext_p : Fext p = 1 := by
    simpa [hφp] using hFext_eq p hpW
  let V : Set M := W ∩ Fext ⁻¹' ({0}ᶜ : Set ℝ)
  refine ⟨V, ?_, ?_, ?_⟩
  · -- The nonvanishing locus is open relative to the extension neighborhood because `Fext` is
    -- continuous there.
    exact hFext_smooth.continuousOn.isOpen_inter_preimage hW_open isOpen_compl_singleton
  · -- The extension takes the value `1` at the base point, so the base point lies in this
    -- nonvanishing ambient neighborhood.
    refine ⟨hpW, ?_⟩
    simpa [hFext_p]
  · -- Any subtype point in that ambient nonvanishing locus is a genuine support point of `φ`,
    -- hence belongs to the prescribed support patch `U`.
    intro x hxV
    have hxW : (x : M) ∈ W := hxV.1
    have hx_nonzero : Fext x ≠ 0 := hxV.2
    have hφ_nonzero : φ x ≠ 0 := by
      rw [hFext_eq x hxW] at hx_nonzero
      exact hx_nonzero
    have hx_support : x ∈ Function.support (φ : S → ℝ) :=
      Function.mem_support.mpr hφ_nonzero
    have hx_tsupport : x ∈ tsupport (φ : S → ℝ) :=
      subset_tsupport (φ : S → ℝ) hx_support
    exact hφsupport hx_tsupport

/-- Helper for Problem 5-18: if every point of `S` has enough ambient-open neighborhood
refinements to recover its intrinsic open neighborhoods, then the subtype inclusion carries the
given topology on `S` to the induced subspace topology on `M`. -/
lemma subtype_val_isEmbedding_of_local_ambient_refinements
    (hRefine :
      ∀ p : S, ∀ U : Set S, IsOpen U → p ∈ U →
        ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ {x : S | x.1 ∈ V} ⊆ U) :
    Topology.IsEmbedding (Subtype.val : S → M) := by
  -- Route correction: in this codebase `S` is already the subtype with its induced topology, so
  -- the ambient inclusion is the canonical subtype embedding independently of `hRefine`.
  let _ := hRefine
  simpa using Topology.IsEmbedding.subtypeVal

/-- Helper for Problem 5-18: an open subset of the submanifold subtype is cut out by an ambient
open subset of `M`. -/
lemma subtype_open_eq_preimage_ambient_open {U : Set S} (hU : IsOpen U) :
    ∃ V : Set M, IsOpen V ∧ U = {x : S | x.1 ∈ V} := by
  -- Open sets in the subtype topology are exactly preimages of ambient open sets along the
  -- canonical inclusion.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp hU with ⟨V, hV_open, hV_eq⟩
  exact ⟨V, hV_open, hV_eq.symm⟩

/-- Helper for Problem 5-18: on the source chart of an immersion normal form, projecting ambient
chart coordinates back to the source factor recovers the intrinsic source coordinates. -/
lemma immersion_projection_eq_domain_coordinates
    {p q : S}
    (hImm : Manifold.IsImmersionAt J I ⊤ (Subtype.val : S → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[ℝ] E' :=
      (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
        hImm.equiv.symm.toContinuousLinearMap
    π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q := by
  -- Apply the chosen projection to the chart normal form and simplify the chart inverses.
  let π : E →L[ℝ] E' :=
    (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
      hImm.equiv.symm.toContinuousLinearMap
  have hq_source : q ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source (I := J)] using hq
  have hq_target : (hImm.domChart.extend J) q ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  simpa [π, Function.comp, ContinuousLinearMap.comp_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

/-- Helper for Problem 5-18: an embedded submanifold admits a smooth ambient scalar extension near
each point of the submanifold. -/
lemma embedded_pointwise_local_scalar_extension
    (hEmb : IsEmbeddedSubmanifold I J S)
    (f : C^∞⟮J, S; ℝ⟯) (p : S) :
    ∃ V : Set M,
      IsOpen V ∧
        (p : M) ∈ V ∧
          ∃ Fext : M → ℝ,
            ContMDiffOn I 𝓘(ℝ) ∞ Fext V ∧
              ∀ q : S, (q : M) ∈ V → Fext q = f q := by
  let hImm : Manifold.IsImmersionAt J I ⊤ (Subtype.val : S → M) p :=
    hEmb.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt p
  let π : E →L[ℝ] E' :=
    (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
      hImm.equiv.symm.toContinuousLinearMap
  let fcoord : E' → ℝ := fun z ↦ f ((hImm.domChart.extend J).symm z)
  have hdomChart_symm :
      ContMDiffOn 𝓘(ℝ, E') J ∞ (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    -- Rewrite the standard smoothness theorem for the inverse extended chart onto its natural
    -- target.
    convert contMDiffOn_extend_symm (I := J) (n := (∞ : ℕ∞ω))
      (IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
        (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω)) (by simp) hImm.domChart_mem_maximalAtlas) using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  -- Express the intrinsic smooth function in the source chart coordinates of the immersion.
  have hfcoord :
      ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ) ∞ fcoord (hImm.domChart.extend J).target := by
    simpa [fcoord, Function.comp] using f.contMDiff.comp_contMDiffOn hdomChart_symm
  rcases subtype_open_eq_preimage_ambient_open (M := M) (S := S)
      (U := hImm.domChart.source) hImm.domChart.open_source with
    ⟨W, hW_open, hW_eq⟩
  have hpW : (p : M) ∈ W := by
    simpa [hW_eq] using hImm.mem_domChart_source
  let T : Set E' := interior ((hImm.domChart.extend J).target)
  have hT_open : IsOpen T := isOpen_interior
  have hT_sub : T ⊆ (hImm.domChart.extend J).target := interior_subset
  have hpT : (hImm.domChart.extend J) p ∈ T := by
    exact
      (J.isInteriorPoint_iff_of_mem_maximalAtlas
        (n := (⊤ : ℕ∞ω)) (hn := by simp)
        hImm.domChart_mem_maximalAtlas hImm.mem_domChart_source).1
        BoundarylessManifold.isInteriorPoint
  have hp_proj :
      π ((hImm.codChart.extend I) p) = (hImm.domChart.extend J) p :=
    immersion_projection_eq_domain_coordinates (I := I) (J := J) hImm hImm.mem_domChart_source
  have hp_projT : (π ∘ (hImm.codChart.extend I)) p ∈ T := by
    simpa [Function.comp] using hp_proj.symm ▸ hpT
  have hπ_cont :
      ContinuousAt (π ∘ (hImm.codChart.extend I)) p := by
    exact π.continuous.continuousAt.comp
      (hImm.codChart.continuousAt_extend (I := I) hImm.mem_codChart_source)
  have hpre :
      ((π ∘ (hImm.codChart.extend I)) ⁻¹' T) ∈ nhds (p : M) := by
    exact hπ_cont.preimage_mem_nhds (hT_open.mem_nhds hp_projT)
  rcases mem_nhds_iff.mp hpre with ⟨V₀, hV₀_sub, hV₀_open, hpV₀⟩
  let V : Set M := hImm.codChart.source ∩ (W ∩ V₀)
  let Fext : M → ℝ := fcoord ∘ π ∘ (hImm.codChart.extend I)
  have hcod_ext :
      ContMDiffOn I 𝓘(ℝ, E) ∞ (hImm.codChart.extend I) V := by
    exact
      (contMDiffOn_extend (I := I) (n := (∞ : ℕ∞ω))
        (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
          (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω)) (by simp) hImm.codChart_mem_maximalAtlas)).mono
        fun _x hx ↦ hx.1
  have hproj :
      ContMDiffOn I 𝓘(ℝ, E') ∞ (π ∘ (hImm.codChart.extend I)) V := by
    simpa [Function.comp] using π.contDiff.contMDiff.comp_contMDiffOn hcod_ext
  have hmaps :
      Set.MapsTo (π ∘ (hImm.codChart.extend I)) V (hImm.domChart.extend J).target := by
    intro x hx
    exact hT_sub (hV₀_sub hx.2.2)
  have hFext :
      ContMDiffOn I 𝓘(ℝ) ∞ Fext V := by
    -- Compose the chart representative with the codomain-chart coordinates projected back to the
    -- source factor of the immersion normal form.
    exact hfcoord.comp hproj hmaps
  refine ⟨V, ?_, ?_, Fext, hFext, ?_⟩
  · -- The ambient neighborhood simultaneously stays inside the codomain chart, the ambient patch
    -- realizing the source chart domain, and the projected-coordinate target neighborhood.
    exact hImm.codChart.open_source.inter (hW_open.inter hV₀_open)
  · -- The base point lies in all three defining neighborhoods by construction.
    exact ⟨hImm.mem_codChart_source, hpW, hpV₀⟩
  · intro q hqV
    have hqW : (q : M) ∈ W := hqV.2.1
    have hq_dom : q ∈ hImm.domChart.source := by
      simpa [hW_eq] using hqW
    have hq_proj :
        π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
      immersion_projection_eq_domain_coordinates (I := I) (J := J) hImm hq_dom
    -- On the submanifold patch, the projected ambient coordinates are exactly the intrinsic chart
    -- coordinates, so the ambient formula reduces to the original function.
    calc
      Fext q = fcoord (π ((hImm.codChart.extend I) q)) := rfl
      _ = f ((hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q))) := rfl
      _ = f ((hImm.domChart.extend J).symm ((hImm.domChart.extend J) q)) := by rw [hq_proj]
      _ = f q := by
            rw [hImm.domChart.extend_left_inv (I := J) hq_dom]

-- Proof sketch: for an embedded submanifold, the local slice model makes each intrinsically smooth
-- real-valued function locally extend to the ambient manifold, exactly the owner
-- `Function.IsSmoothOn`. Conversely, if every smooth real-valued function has that pointwise local
-- extension property, then the immersed submanifold is embedded in the sense of the chapter owner
-- `IsEmbeddedSubmanifold`.
/-- Problem 5-18 (1): (a) For an immersed smooth submanifold, being embedded is equivalent to the
pointwise local ambient extension property for every intrinsically smooth real-valued function. We
state the local condition using the existing owner `Function.IsSmoothOn`. -/
theorem immersed_submanifold_isEmbeddedSubmanifold_iff_smoothFunctions_isSmoothOn
    (hS : IsImmersedSubmanifold I J S) :
    IsEmbeddedSubmanifold I J S ↔
      ∀ f : C^⊤⟮J, S; ℝ⟯, (f : S → ℝ).IsSmoothOn I 𝓘(ℝ) := by
  constructor
  · intro hEmb
    intro f
    rw [Function.isSmoothOn_iff_exists_local_extension]
    have hfInf : ContMDiff J 𝓘(ℝ) ∞ f := by
      -- A top-order scalar map is in particular `C^∞`.
      exact f.contMDiff.of_le (by simp)
    let fInf : C^∞⟮J, S; ℝ⟯ := ⟨f, hfInf⟩
    intro p
    -- Use the local immersion normal form of the embedded inclusion at `p` to build the ambient
    -- extension directly in coordinates.
    rcases embedded_pointwise_local_scalar_extension (I := I) (J := J) (S := S) hEmb fInf p with
      ⟨V, hV_open, hpV, Fext, hFext, hEq⟩
    refine ⟨V, hV_open, hpV, Fext, hFext, ?_⟩
    intro q hqV
    simpa [fInf] using hEq q hqV
  · intro hExt
    -- Route correction: for the subtype-based owner used in this development, the topological
    -- embedding part is already built into `Subtype.val`, so only the stored immersion matters.
    refine
      { toBoundarylessManifold := ‹BoundarylessManifold J S›
        isSmoothEmbedding_subtype_val := ?_ }
    -- Package the existing immersion with the canonical subtype embedding.
    exact ⟨hS, Topology.IsEmbedding.subtypeVal⟩

section GlobalExtension

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

/-- Helper for Problem 5-18: at any point of an immersed submanifold in a finite-dimensional
ambient manifold, the model space of the submanifold is automatically finite-dimensional. -/
lemma finiteDimensional_modelSpace_of_immersed_submanifold_point
    (hS : IsImmersedSubmanifold I J S) (p : S) :
    FiniteDimensional ℝ E' := by
  let hImm : Manifold.IsImmersionAt J I ⊤ (Subtype.val : S → M) p :=
    hS.isImmersionAt p
  let _ : FiniteDimensional ℝ (E' × hImm.complement) :=
    FiniteDimensional.of_injective hImm.equiv.toLinearMap hImm.equiv.injective
  exact
    FiniteDimensional.of_injective
      (ContinuousLinearMap.inl ℝ E' hImm.complement).toLinearMap
      LinearMap.inl_injective

/-- Helper for Problem 5-18: a global smooth ambient extension of every scalar function on `S`
immediately implies the local extension property `Function.IsSmoothOn`. -/
lemma smoothFunctions_isSmoothOn_of_global_extension
    (hExt :
      ∀ f : C^∞⟮J, S; ℝ⟯, ∃ g : C^∞⟮I, M; ℝ⟯, ∀ x : S, g x = f x) :
    ∀ f : C^⊤⟮J, S; ℝ⟯, (f : S → ℝ).IsSmoothOn I 𝓘(ℝ) := by
  intro f
  rw [Function.isSmoothOn_iff_exists_local_extension]
  have hfInf : ContMDiff J 𝓘(ℝ) ∞ f := by
    -- The reverse implication only needs a bundled `C^∞` source map, so lower the given
    -- top-order map once here.
    exact f.contMDiff.of_le (by simp)
  let fInf : C^∞⟮J, S; ℝ⟯ := ⟨f, hfInf⟩
  rcases hExt fInf with ⟨g, hg⟩
  intro x
  -- Use the global extension itself as the local extension on the ambient-open set `univ`.
  refine ⟨Set.univ, isOpen_univ, by simp, g, ?_, ?_⟩
  · -- A globally smooth map is smooth on the whole ambient manifold.
    simpa using (g.contMDiff.contMDiffOn : ContMDiffOn I 𝓘(ℝ) ∞ g Set.univ)
  · -- The extension hypothesis identifies `g` with `f` on the subtype.
    intro y hy
    simpa [fInf] using hg y

/-- Helper for Problem 5-18: packaging a scalar local extension into the preferred `ℝ¹` model
preserves the owner predicate `Function.IsSmoothOn`. -/
lemma real_to_r1_isSmoothOn_of_real_isSmoothOn
    {f : S → ℝ} (hf : f.IsSmoothOn I 𝓘(ℝ)) :
    (fun x : S ↦ real_to_r1 (f x)).IsSmoothOn I (𝓡 1) := by
  rw [Function.isSmoothOn_iff_exists_local_extension] at hf ⊢
  intro x
  rcases hf x with ⟨V, hV_open, hxV, Fext, hFext, hEq⟩
  refine ⟨V, hV_open, hxV, real_to_r1 ∘ Fext, ?_, ?_⟩
  · -- Postcompose each scalar local extension with the fixed linear identification `ℝ ≃ ℝ¹`.
    simpa [real_to_r1, Function.comp] using
      real_to_r1_equiv.toContinuousLinearMap.contMDiff.comp_contMDiffOn hFext
  · -- On the subtype, the packaged extension is exactly the original scalar value.
    intro y hy
    simp [hEq y hy, real_to_r1]

/-- Helper for Problem 5-18: the closed-subset extension lemma yields a global ambient extension at
the bundled owner `C^∞`. -/
lemma smoothFunctions_extend_globally_as_C_infty
    (hS : IsImmersedSubmanifold I J S)
    (hEmb : IsEmbeddedSubmanifold I J S) (hProper : S.IsProperlyEmbedded)
    (f : C^∞⟮J, S; ℝ⟯) :
    ∃ g : C^∞⟮I, M; ℝ⟯, ∀ x : S, g x = f x := by
  let _ := hS
  letI : IsManifold I ∞ M := IsManifold.of_le le_top
  have hSmoothOn :
      (f : S → ℝ).IsSmoothOn I 𝓘(ℝ) := by
    -- The local slice-chart extension from embeddedness already packages exactly the closed-set
    -- extension hypothesis needed by Lemma 2.26.
    rw [Function.isSmoothOn_iff_exists_local_extension]
    intro p
    rcases embedded_pointwise_local_scalar_extension (I := I) (J := J) (S := S) hEmb f p with
      ⟨V, hV_open, hpV, Fext, hFext, hEq⟩
    exact ⟨V, hV_open, hpV, Fext, hFext, hEq⟩
  let f₁ : S → EuclideanSpace ℝ (Fin 1) := fun x ↦ real_to_r1 (f x)
  have hSmoothOn₁ :
      f₁.IsSmoothOn I (𝓡 1) :=
    real_to_r1_isSmoothOn_of_real_isSmoothOn (I := I) (S := S) hSmoothOn
  have hClosed : IsClosed S := hProper.isClosed
  rcases exists_supported_contMDiffMap_extension_of_isClosed
      (M := M) (I := I) (A := S) (U := Set.univ) hClosed isOpen_univ (by intro x hx; simp)
      f₁ hSmoothOn₁ with
    ⟨F, hF_eq, _hF_support⟩
  let proj0 :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), EuclideanSpace ℝ (Fin 1); 𝓘(ℝ), ℝ⟯ :=
    (((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)) :
      EuclideanSpace ℝ (Fin 1) →L[ℝ] ℝ) :
      C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin 1)), EuclideanSpace ℝ (Fin 1); 𝓘(ℝ), ℝ⟯)
  -- Recover the scalar extension by taking the unique coordinate of the global `ℝ¹` extension.
  refine ⟨proj0.comp F, ?_⟩
  intro x
  simpa [f₁, proj0, real_to_r1_apply_zero] using
    congrArg (fun v : EuclideanSpace ℝ (Fin 1) ↦ v 0) (hF_eq x)

/-- Helper for Problem 5-18: the subtype inclusion of an embedded submanifold is globally smooth
as a map to the ambient manifold. -/
lemma subtype_val_contMDiff_of_isEmbeddedSubmanifold
    (hEmb : IsEmbeddedSubmanifold I J S) :
    ContMDiff J I ⊤ (Subtype.val : S → M) := by
  have hSmoothTop : ContMDiff J I (⊤ : WithTop ℕ∞) (Subtype.val : S → M) := by
    intro x
    let hImmAt : Manifold.IsImmersionAt J I ⊤ (Subtype.val : S → M) x :=
      hEmb.isSmoothEmbedding_subtype_val.isImmersion.isImmersionAt x
    let x' : E' := (hImmAt.domChart.extend J) x
    let L : E' →L[ℝ] E :=
      hImmAt.equiv.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ E' hImmAt.complement)
    -- The subtype inclusion is the canonical continuous map into the ambient manifold.
    have hcont : ContinuousAt (Subtype.val : S → M) x :=
      continuous_subtype_val.continuousAt
    have hx : x ∈ hImmAt.domChart.source := hImmAt.mem_domChart_source
    have hy : (Subtype.val : S → M) x ∈ hImmAt.codChart.source := hImmAt.mem_codChart_source
    -- Rewrite the inclusion in immersion charts and replace it by the linear map `u ↦ (u, 0)`.
    rw [ContMDiffAt, contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ)
      (e := hImmAt.domChart) (e' := hImmAt.codChart) hImmAt.domChart_mem_maximalAtlas
      hImmAt.codChart_mem_maximalAtlas hx hy, continuousWithinAt_univ, Set.preimage_univ,
      Set.univ_inter]
    refine ⟨hcont, ?_⟩
    have hmodel : ContDiffWithinAt ℝ (⊤ : WithTop ℕ∞) L (Set.range J) x' := by
      exact L.contDiff.contDiffWithinAt
    have htarget_mem : (hImmAt.domChart.extend J).target ∈ nhdsWithin x' (Set.range J) := by
      simpa [x'] using hImmAt.domChart.extend_target_mem_nhdsWithin (I := J) hx
    have hEq :
        ((hImmAt.codChart.extend I) ∘ (Subtype.val : S → M) ∘ (hImmAt.domChart.extend J).symm)
          =ᶠ[nhdsWithin x' (Set.range J)] L := by
      refine Filter.eventuallyEq_of_mem htarget_mem ?_
      intro z hz
      simpa [Function.comp, L] using hImmAt.writtenInCharts hz
    have hx'_target : x' ∈ (hImmAt.domChart.extend J).target :=
      (hImmAt.domChart.extend J).map_source <| by
        simpa [OpenPartialHomeomorph.extend_source] using hx
    have hx'_range : x' ∈ Set.range J :=
      hImmAt.domChart.extend_target_subset_range hx'_target
    exact hmodel.congr_of_eventuallyEq hEq <| hEq.eq_of_nhdsWithin hx'_range
  exact hSmoothTop.of_le le_top

/-- Helper for Problem 5-18: a properly embedded submanifold admits global bundled `C^∞` scalar
extensions because the pointwise local ambient extensions over the closed subset glue via the
closed-subset extension theorem. -/
lemma properly_embedded_scalar_global_extension_top
    (hEmb : IsEmbeddedSubmanifold I J S) (hProper : S.IsProperlyEmbedded)
    (f : C^∞⟮J, S; ℝ⟯) :
    ∃ g : C^∞⟮I, M; ℝ⟯, ∀ x : S, g x = f x := by
  have hS : IsImmersedSubmanifold I J S :=
    hEmb.isSmoothEmbedding_subtype_val.isImmersion
  -- Route correction: the correct owner here is bundled `C^∞`, matching the actual extension API.
  exact smoothFunctions_extend_globally_as_C_infty (I := I) (J := J) (S := S) hS hEmb hProper f

/-- Helper for Problem 5-18: a point of the submanifold determines a point of the punctured
ambient manifold whenever the removed point does not lie on the submanifold. -/
lemma subtype_val_ne_puncture
    {p : M} (hpS : p ∉ S) (x : S) :
    (x : M) ≠ p := by
  intro hxp
  exact hpS (hxp ▸ x.2)

/-- Helper for Problem 5-18: the inclusion of `S` into the punctured ambient open subtype obtained
by removing a point outside `S`. -/
def subtype_val_to_punctured_ambient {p : M} (hpS : p ∉ S) :
    let U : TopologicalSpace.Opens M := ⟨{x : M | x ≠ p}, isOpen_compl_singleton⟩
    S → U :=
  fun x ↦ ⟨(x : M), subtype_val_ne_puncture (S := S) hpS x⟩

/-- Helper for Problem 5-18: after removing an ambient point `p ∉ S`, the subtype inclusion
codomain-restricts smoothly to the punctured ambient open subset. -/
lemma subtype_val_to_punctured_ambient_contMDiff
    (hEmb : IsEmbeddedSubmanifold I J S) {p : M} (hpS : p ∉ S) :
    let U : TopologicalSpace.Opens M := ⟨{x : M | x ≠ p}, isOpen_compl_singleton⟩
    ContMDiff J I ⊤ (subtype_val_to_punctured_ambient (M := M) (S := S) hpS) := by
  let U : TopologicalSpace.Opens M := ⟨{x : M | x ≠ p}, isOpen_compl_singleton⟩
  -- Codomain restriction into an open subset preserves smoothness of the ambient inclusion.
  simpa [U, Set.codRestrict] using
    contMDiff_codRestrict_opens (I := I) (K := J) U
      (subtype_val_contMDiff_of_isEmbeddedSubmanifold (I := I) (J := J) (S := S) hEmb)
      (subtype_val_ne_puncture (S := S) hpS)

/-- Helper for Problem 5-18: the punctured ambient open subtype carries a positive bundled `C^∞`
smooth exhaustion function. -/
lemma punctured_open_positive_exhaustion_top (p : M) :
    let U : TopologicalSpace.Opens M := ⟨{x : M | x ≠ p}, isOpen_compl_singleton⟩
    ∃ h : C^∞⟮I, U; ℝ⟯, (∀ x : U, 0 < h x) ∧ (h : U → ℝ).IsExhaustionFunction := by
  letI : IsManifold I ∞ M := IsManifold.of_le le_top
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (H := H) (M := M)
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let U : TopologicalSpace.Opens M := ⟨{x : M | x ≠ p}, isOpen_compl_singleton⟩
  letI : SecondCountableTopology U := inferInstance
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : IsManifold I ∞ U := inferInstance
  -- Proposition 2.28 applies directly to the punctured ambient open subtype once the manifold
  -- regularity is lowered from `⊤` to `∞`.
  simpa [U] using exists_positive_smooth_exhaustion_function (I := I) (M := U)

/-- Helper for Problem 5-18: intersecting with an open neighborhood preserves closure membership
at the center point. -/
lemma mem_closure_inter_of_mem_closure
    {p : M} {A N : Set M}
    (hpA : p ∈ closure A) (hN_open : IsOpen N) (hpN : p ∈ N) :
    p ∈ closure (A ∩ N) := by
  rw [mem_closure_iff_nhds]
  intro Z hZ
  have hZN : Z ∩ N ∈ nhds p := Filter.inter_mem hZ (hN_open.mem_nhds hpN)
  rcases mem_closure_iff_nhds.1 hpA (Z ∩ N) hZN with ⟨y, hyZN, hyA⟩
  exact ⟨y, hyZN.1, hyA, hyZN.2⟩

/-- Helper for Problem 5-18: if a point lies in `closure S \ S`, then the restriction to `S` of a
positive exhaustion function on the punctured ambient manifold cannot extend to a global bundled
`C^∞` ambient scalar function. -/
lemma punctured_ambient_exhaustion_nonextendable
    (hEmb : IsEmbeddedSubmanifold I J S) {p : M}
    (hp_closure : p ∈ closure S) (hpS : p ∉ S) :
    ∃ f : C^∞⟮J, S; ℝ⟯,
      ¬ ∃ g : C^∞⟮I, M; ℝ⟯, ∀ x : S, g x = f x := by
  letI : IsManifold I ∞ M := IsManifold.of_le le_top
  letI : IsManifold J ∞ S := IsManifold.of_le le_top
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (H := H) (M := M)
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  let U : TopologicalSpace.Opens M := ⟨{x : M | x ≠ p}, isOpen_compl_singleton⟩
  letI : SecondCountableTopology U := inferInstance
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : IsManifold I ∞ U := inferInstance
  rcases (show ∃ h : C^∞⟮I, U; ℝ⟯, (∀ x : U, 0 < h x) ∧ (h : U → ℝ).IsExhaustionFunction by
      simpa [U] using punctured_open_positive_exhaustion_top (I := I) (M := M) p) with
    ⟨h, hpos, hExhaust⟩
  have hi_contMDiff :
      ContMDiff J I ∞ (subtype_val_to_punctured_ambient (M := M) (S := S) hpS) := by
    -- The inclusion into the punctured ambient open subtype is smooth after lowering to `∞`.
    exact
      (subtype_val_to_punctured_ambient_contMDiff (I := I) (J := J) (S := S) hEmb
        (p := p) hpS).of_le (by simp)
  let iSU : C^∞⟮J, S; I, U⟯ :=
    ⟨subtype_val_to_punctured_ambient (M := M) (S := S) hpS, hi_contMDiff⟩
  let f : C^∞⟮J, S; ℝ⟯ := h.comp iSU
  refine ⟨f, ?_⟩
  intro hgExt
  rcases hgExt with ⟨g, hg⟩
  let N : Set M := g ⁻¹' Set.Iio (g p + 1)
  have hN_open : IsOpen N := by
    -- Bound the hypothetical ambient extension above by `g p + 1` on an ambient-open neighborhood.
    exact g.contMDiff.continuous.isOpen_preimage _ isOpen_Iio
  have hpN : p ∈ N := by
    -- The base point itself satisfies this upper bound strictly.
    have hlt : g p < g p + 1 := by linarith
    simpa [N] using hlt
  have hp_closure_inter : p ∈ closure (S ∩ N) :=
    mem_closure_inter_of_mem_closure (p := p) (A := S) (N := N) hp_closure hN_open hpN
  let K : Set U := (h : U → ℝ) ⁻¹' Set.Iic (g p + 1)
  have hK_compact : IsCompact K := hExhaust.isCompact_sublevelSet (g p + 1)
  have hK_closed_image : IsClosed (Subtype.val '' K) := by
    -- Compact subsets of the Hausdorff ambient manifold are closed.
    exact (hK_compact.image continuous_subtype_val).isClosed
  have hsubset_image : S ∩ N ⊆ Subtype.val '' K := by
    intro x hx
    let xS : S := ⟨x, hx.1⟩
    have hx_ne : x ≠ p := subtype_val_ne_puncture (S := S) hpS xS
    let xU : U := ⟨x, hx_ne⟩
    have hxle : h xU ≤ g p + 1 := by
      have hgx : g x = f xS := by
        simpa [f] using hg xS
      have hxlt : g x < g p + 1 := by
        simpa [N] using hx.2
      calc
        h xU = f xS := by
          simp [f, iSU, subtype_val_to_punctured_ambient, xU, xS]
        _ = g x := hgx.symm
        _ ≤ g p + 1 := le_of_lt hxlt
    refine ⟨xU, ?_, rfl⟩
    simpa [K] using hxle
  have hp_not_image : p ∉ Subtype.val '' K := by
    intro hpImage
    rcases hpImage with ⟨x, -, hx⟩
    exact x.2 hx
  have hp_not_closure_inter : p ∉ closure (S ∩ N) := by
    -- The punctured compact image is closed and misses `p`, so its subset `S ∩ N` also has
    -- closure missing `p`.
    exact fun hp ↦ hp_not_image (closure_minimal hsubset_image hK_closed_image hp)
  exact hp_not_closure_inter hp_closure_inter

/-- Helper for Problem 5-18: in this notation layer the bundled target `C^⊤` is strictly
stronger than the available global extension owner `C^∞`, so a `C^∞` map cannot be downgraded to
`C^⊤` by `ContMDiff.of_le`. -/
lemma bundled_top_order_not_le_c_infty :
    ¬ (((⊤ : WithTop ℕ∞) : ℕ∞ω) ≤ (∞ : ℕ∞ω)) := by
  -- The coercion sends `⊤ : WithTop ℕ∞` to the finite order `ω`, which is not below `∞`.
  simp

-- Proof sketch: by part (a), embeddedness gives the `Function.IsSmoothOn` hypothesis for every
-- smooth function on `S`. If `S` is properly embedded, then in a `T₁` ambient manifold it is
-- closed, so the project extension lemma for closed subsets upgrades the pointwise local
-- extensions to a global smooth extension on `M`. Conversely, global extensions restrict to local
-- ones and force proper embeddedness via closedness of the image.
/-- Problem 5-18 (2): (b) On a Hausdorff `σ`-compact finite-dimensional ambient manifold, an
immersed smooth submanifold is properly embedded exactly when every intrinsically smooth
real-valued function on it extends to a global smooth function on the ambient manifold. -/
theorem immersed_submanifold_properlyEmbedded_iff_smoothFunctions_extend_globally
    (hS : IsImmersedSubmanifold I J S) :
    (IsEmbeddedSubmanifold I J S ∧ S.IsProperlyEmbedded) ↔
      ∀ f : C^∞⟮J, S; ℝ⟯, ∃ g : C^∞⟮I, M; ℝ⟯, ∀ x : S, g x = f x := by
  constructor
  · rintro ⟨hEmb, hProper⟩ f
    -- The forward direction is exactly the repaired global `C^∞` extension lemma.
    exact smoothFunctions_extend_globally_as_C_infty (I := I) (J := J) (S := S) hS hEmb hProper f
  · intro hExt
    have hSmoothOn :
        ∀ f : C^⊤⟮J, S; ℝ⟯, (f : S → ℝ).IsSmoothOn I 𝓘(ℝ) :=
      smoothFunctions_isSmoothOn_of_global_extension (I := I) (J := J) (S := S) hExt
    have hEmb : IsEmbeddedSubmanifold I J S :=
      (immersed_submanifold_isEmbeddedSubmanifold_iff_smoothFunctions_isSmoothOn
        (I := I) (J := J) (S := S) hS).2 hSmoothOn
    have hClosed : IsClosed S := by
      classical
      by_contra hNotClosed
      have hnotSubset : ¬ closure S ⊆ S := by
        intro hclosureSub
        apply hNotClosed
        rw [← closure_eq_iff_isClosed]
        exact subset_antisymm hclosureSub subset_closure
      have hpWitness : ∃ p : M, p ∈ closure S ∧ p ∉ S := by
        by_contra hNoWitness
        apply hnotSubset
        intro p hpClosure
        by_contra hpS
        exact hNoWitness ⟨p, hpClosure, hpS⟩
      rcases hpWitness with ⟨p, hpClosure, hpS⟩
      rcases punctured_ambient_exhaustion_nonextendable (I := I) (J := J) (S := S)
          hEmb (p := p) hpClosure hpS with ⟨f, hf⟩
      exact hf (hExt f)
    refine ⟨hEmb, ?_⟩
    -- In a Hausdorff ambient manifold, proper embeddedness is equivalent to closedness.
    simpa using (Set.isProperlyEmbedded_iff_isClosed (S := S)).2 hClosed

end GlobalExtension

end

/-! ### Proposition_5_18 (from Chap05/Sec05_31) -/
open Manifold
open scoped Manifold ContDiff

universe u𝕜 uE uH uM uE' uN uE'' uS

section

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {I : ModelWithCorners 𝕜 E H} [IsManifold I (⊤ : WithTop ℕ∞) M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace E' N]
variable [IsManifold (modelWithCornersSelf 𝕜 E') (⊤ : WithTop ℕ∞) N]

-- Semantic recall note: `lean_leansearch` was unavailable in this session, so the statement
-- surface was chosen from the local `Manifold.ImmersedSubmanifold` and
-- `IsImmersion.toImmersedSubmanifold` API in §5.31.
/-- Proposition 5.18 (1): an injective smooth immersion `F : N → M` determines an immersed
submanifold of `M` whose carrier is exactly `Set.range F`, and `F` identifies `N` diffeomorphically
with that immersed-submanifold image. -/
theorem injective_immersion_range_has_immersed_submanifold_structure {F : N → M}
    (hF : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) F)
    (hFinj : Function.Injective F) :
    ∃ T : Manifold.ImmersedSubmanifold I M,
      T.carrier = Set.range F ∧
        ∃ Φ : N ≃ₘ⟮modelWithCornersSelf 𝕜 E', modelWithCornersSelf 𝕜 T.ModelSpace⟯ T,
          ∀ x : N, T.inclusion (Φ x) = F x := sorry

/-- Proposition 5.18 (2): if another smooth manifold `S` immerses injectively into `M` with the
same image as `F`, then `S` is diffeomorphic to `N` through the ambient maps. This expresses the
uniqueness of the topology and smooth structure on the image of `F` as an immersed submanifold. -/
theorem injective_immersion_range_immersed_submanifold_structure_unique {F : N → M}
    (hF : IsImmersion (modelWithCornersSelf 𝕜 E') I (⊤ : WithTop ℕ∞) F)
    (hFinj : Function.Injective F)
    {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
    {S : Type uS} [TopologicalSpace S] [ChartedSpace E'' S]
    [IsManifold (modelWithCornersSelf 𝕜 E'') (⊤ : WithTop ℕ∞) S]
    {ι : S → M}
    (hιinj : Function.Injective ι)
    (hι : IsImmersion (modelWithCornersSelf 𝕜 E'') I (⊤ : WithTop ℕ∞) ι)
    (hRange : Set.range ι = Set.range F) :
    ∃ Φ : N ≃ₘ⟮modelWithCornersSelf 𝕜 E', modelWithCornersSelf 𝕜 E''⟯ S,
      ∀ x : N, ι (Φ x) = F x := sorry

end
