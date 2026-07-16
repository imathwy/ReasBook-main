import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap05.Sec05_34.Notation_5_34_extra_1
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap01.Sec01_06.Theorem_1_46
import Mathlib.Geometry.Manifold.PartitionOfUnity

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

universe uE uH uM uE' uH'

-- Semantic recall note: `lean_leansearch` surfaced manifold smooth-extension owners from
-- `SmoothApprox`; the source item is kept on the chapter's embedded-submanifold surface instead of
-- being replaced by a closed-subset reformulation.

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [SigmaCompactSpace M]
variable {I : ModelWithCorners ℝ E H} [IsManifold I ∞ M]
variable {S : Set M}
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H']
variable {J : ModelWithCorners ℝ E' H'} [ChartedSpace H' S] [IsManifold J ∞ S]

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]
  [IsManifold I ∞ M] [IsManifold J ∞ S] in
/-- Helper for Lemma 5.34: in the local normal form of the embedded inclusion, projecting ambient
chart coordinates to the source factor recovers the intrinsic source coordinates. -/
lemma immersionProjectionEqDomainCoordinates
    {p q : S}
    {n : ℕ∞ω} (hImm : Manifold.IsImmersionAt J I n (Subtype.val : S → M) p)
    (hq : q ∈ hImm.domChart.source) :
    let π : E →L[ℝ] E' :=
      (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
        hImm.equiv.symm.toContinuousLinearMap
    π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q := by
  let π : E →L[ℝ] E' :=
    (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
      hImm.equiv.symm.toContinuousLinearMap
  -- Apply the chosen projection to the immersion chart normal form and simplify the chart inverses.
  have hq_source : q ∈ (hImm.domChart.extend J).source := by
    simpa [hImm.domChart.extend_source (I := J)] using hq
  have hq_target : (hImm.domChart.extend J) q ∈ (hImm.domChart.extend J).target :=
    (hImm.domChart.extend J).map_source hq_source
  have hcoords := congrArg π (hImm.writtenInCharts hq_target)
  simpa [π, Function.comp, ContinuousLinearMap.comp_apply,
    OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm, hq] using hcoords

/-- Helper for Lemma 5.34: an embedded smooth submanifold admits a smooth ambient scalar extension
near each of its points. -/
lemma embeddedPointwiseLocalScalarExtension
    [IsEmbeddedSubmanifold I J S] (f : C^∞⟮J, S; ℝ⟯) (p : S) :
    ∃ V : Set M,
      IsOpen V ∧
        (p : M) ∈ V ∧
          ∃ Fext : M → ℝ,
            ContMDiffOn I 𝓘(ℝ) ∞ Fext V ∧
              ∀ q : S, (q : M) ∈ V → Fext q = f q := by
  let hImm : Manifold.IsImmersionAt J I ω (Subtype.val : S → M) p :=
    IsEmbeddedSubmanifold.isSmoothEmbedding_subtype_val
      (I := I) (J := J) (S := S) |>.isImmersion.isImmersionAt p
  let π : E →L[ℝ] E' :=
    (ContinuousLinearMap.fst ℝ E' hImm.complement).comp
      hImm.equiv.symm.toContinuousLinearMap
  let fcoord : E' → ℝ := fun z ↦ f ((hImm.domChart.extend J).symm z)
  -- Rewrite the intrinsic smooth function in the source chart coordinates of the immersion.
  have hdomChart_symm :
      ContMDiffOn 𝓘(ℝ, E') J ∞ (hImm.domChart.extend J).symm
        (hImm.domChart.extend J).target := by
    convert contMDiffOn_extend_symm (I := J) (n := (∞ : ℕ∞ω))
      (IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
        (m := (∞ : ℕ∞ω)) (n := (ω : ℕ∞ω)) (by simp) hImm.domChart_mem_maximalAtlas) using 2
    simpa [Set.inter_comm] using (J.image_eq hImm.domChart.target).symm
  have hfcoord :
      ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ) ∞ fcoord (hImm.domChart.extend J).target := by
    simpa [fcoord, Function.comp] using f.contMDiff.comp_contMDiffOn hdomChart_symm
  -- Convert the intrinsic source-chart domain into an ambient-open patch of `M`.
  rcases Topology.IsInducing.subtypeVal.isOpen_iff.mp hImm.domChart.open_source with
    ⟨W, hW_open, hW_eq⟩
  have hpW : (p : M) ∈ W := by
    have hp_pre : p ∈ Subtype.val ⁻¹' W := by
      rw [hW_eq]
      exact hImm.mem_domChart_source
    exact hp_pre
  let T : Set E' := interior ((hImm.domChart.extend J).target)
  have hT_sub : T ⊆ (hImm.domChart.extend J).target := interior_subset
  have hpT : (hImm.domChart.extend J) p ∈ T := by
    exact
      (J.isInteriorPoint_iff_of_mem_maximalAtlas
        (n := (∞ : ℕ∞ω)) (hn := by simp)
        (IsManifold.maximalAtlas_subset_of_le (I := J) (M := S)
          (m := (∞ : ℕ∞ω)) (n := (ω : ℕ∞ω)) (by simp) hImm.domChart_mem_maximalAtlas)
        hImm.mem_domChart_source).1
        BoundarylessManifold.isInteriorPoint
  have hp_proj :
      π ((hImm.codChart.extend I) p) = (hImm.domChart.extend J) p :=
    immersionProjectionEqDomainCoordinates (I := I) (J := J) hImm hImm.mem_domChart_source
  have hp_projT : (π ∘ (hImm.codChart.extend I)) p ∈ T := by
    simpa [Function.comp] using hp_proj.symm ▸ hpT
  have hπ_cont :
      ContinuousAt (π ∘ (hImm.codChart.extend I)) p := by
    exact π.continuous.continuousAt.comp
      (hImm.codChart.continuousAt_extend (I := I) hImm.mem_codChart_source)
  have hpre :
      ((π ∘ (hImm.codChart.extend I)) ⁻¹' T) ∈ nhds (p : M) := by
    exact hπ_cont.preimage_mem_nhds (isOpen_interior.mem_nhds hp_projT)
  rcases mem_nhds_iff.mp hpre with ⟨V₀, hV₀_sub, hV₀_open, hpV₀⟩
  let V : Set M := hImm.codChart.source ∩ (W ∩ V₀)
  let Fext : M → ℝ := fcoord ∘ π ∘ (hImm.codChart.extend I)
  -- Smoothness on the ambient patch comes from composing the chart representative with the
  -- projected ambient coordinates.
  have hcod_ext :
      ContMDiffOn I 𝓘(ℝ, E) ∞ (hImm.codChart.extend I) V := by
    exact
      (contMDiffOn_extend (I := I) (n := (∞ : ℕ∞ω))
        (IsManifold.maximalAtlas_subset_of_le (I := I) (M := M)
          (m := (∞ : ℕ∞ω)) (n := (ω : ℕ∞ω)) (by simp) hImm.codChart_mem_maximalAtlas)).mono
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
    exact hfcoord.comp hproj hmaps
  refine ⟨V, ?_, ?_, Fext, hFext, ?_⟩
  · -- The ambient neighborhood stays inside the codomain chart, the ambient realization of the
    -- source-chart domain, and the projected-coordinate neighborhood.
    exact hImm.codChart.open_source.inter (hW_open.inter hV₀_open)
  · -- The base point lies in each of the defining pieces of the ambient patch.
    exact ⟨hImm.mem_codChart_source, hpW, hpV₀⟩
  · intro q hqV
    have hqW : (q : M) ∈ W := hqV.2.1
    have hq_dom : q ∈ hImm.domChart.source := by
      have hq_pre : q ∈ Subtype.val ⁻¹' W := hqW
      rw [hW_eq] at hq_pre
      exact hq_pre
    have hq_proj :
        π ((hImm.codChart.extend I) q) = (hImm.domChart.extend J) q :=
      immersionProjectionEqDomainCoordinates (I := I) (J := J) hImm hq_dom
    -- On the source patch, the projected ambient coordinates are exactly the intrinsic chart
    -- coordinates, so the ambient formula reduces to the original function.
    calc
      Fext q = fcoord (π ((hImm.codChart.extend I) q)) := rfl
      _ = f ((hImm.domChart.extend J).symm (π ((hImm.codChart.extend I) q))) := rfl
      _ = f ((hImm.domChart.extend J).symm ((hImm.domChart.extend J) q)) := by rw [hq_proj]
      _ = f q := by
            rw [hImm.domChart.extend_left_inv (I := J) hq_dom]

/-- Lemma 5.34 (1): if `S` is an embedded smooth submanifold of `M`, then every smooth
real-valued function on `S` extends to a smooth real-valued function on some ambient open
neighborhood of `S`. -/
theorem embedded_submanifold_exists_smooth_extension_on_neighborhood
    [IsEmbeddedSubmanifold I J S] (f : C^∞⟮J, S; ℝ⟯) :
    ∃ U : TopologicalSpace.Opens M,
      ∃ hSU : S ⊆ (U : Set M),
        ∃ ftilde : C^∞⟮I, U; ℝ⟯, ∀ x : S, ftilde ⟨(x : M), hSU x.2⟩ = f x := by
  classical
  letI : SecondCountableTopology H := I.secondCountableTopology
  letI : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact (H := H) (M := M)
  letI : LocallyCompactSpace H := I.locallyCompactSpace
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose V hV_open hpV Fext hFext hEq using
    fun p : S ↦ embeddedPointwiseLocalScalarExtension (I := I) (J := J) (S := S) f p
  let Uset : Set M := ⋃ p : S, V p
  let U : TopologicalSpace.Opens M := ⟨Uset, isOpen_iUnion hV_open⟩
  letI : SecondCountableTopology U := inferInstance
  letI : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  letI : SigmaCompactSpace U := sigmaCompactSpace_of_locallyCompact_secondCountable
  letI : IsManifold I ∞ U := inferInstance
  have hSU : S ⊆ (U : Set M) := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hpV ⟨x, hx⟩⟩
  let t : U → Set ℝ := fun x ↦
    if hx : (x : M) ∈ S then {f ⟨(x : M), hx⟩} else Set.univ
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : ((x : U) : M) ∈ S
    · simpa [t, hx] using convex_singleton (f ⟨((x : U) : M), hx⟩)
    · simpa [t, hx] using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  have hloc : ∀ x : U, ∃ W ∈ nhds x, ∃ g : U → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ g W ∧
      ∀ y ∈ W, g y ∈ t y := by
    intro x
    rcases Set.mem_iUnion.1 x.2 with ⟨p, hxVp⟩
    let W : Set U := {y : U | (y : M) ∈ V p}
    let g : U → ℝ := fun y ↦ Fext p y
    refine ⟨W, ?_, g, ?_, ?_⟩
    · -- Use the local extension neighborhood chosen for `p` as a neighborhood of `x` inside `U`.
      exact ((hV_open p).preimage continuous_subtype_val).mem_nhds hxVp
    · -- Restrict the ambient smooth extension to the open subtype `U`.
      exact
        (hFext p).comp
          ((contMDiff_subtype_val : ContMDiff I I ∞ (Subtype.val : U → M)).contMDiffOn)
          fun y hy ↦ hy
    · -- On the chosen patch, the restricted ambient extension lands in the singleton target on
      -- `S` and trivially in `Set.univ` off `S`.
      intro y hyW
      by_cases hyS : (y : M) ∈ S
      · have hyEq : Fext p y = f ⟨(y : M), hyS⟩ := hEq p ⟨(y : M), hyS⟩ hyW
        simp [t, hyS, g, hyEq]
      · simp [t, hyS, g]
  -- Glue the local ambient extensions on the open neighborhood generated by their domains.
  obtain ⟨ftilde, hftilde⟩ : ∃ ftilde : C^∞⟮I, U; ℝ⟯, ∀ x : U, ftilde x ∈ t x := by
    simpa [t] using
      exists_contMDiffMap_forall_mem_convex_of_local (I := I) (M := U) (F := ℝ) ht hloc
  refine ⟨U, hSU, ftilde, ?_⟩
  intro x
  have hxmem : ((⟨(x : M), hSU x.2⟩ : U) : M) ∈ S := x.2
  simpa [t, hxmem] using hftilde ⟨(x : M), hSU x.2⟩

/-- Lemma 5.34 (2): if `S` is properly embedded in `M`, then every smooth real-valued function on
`S` extends to a smooth real-valued function on all of `M`. -/
theorem properly_embedded_submanifold_exists_global_smooth_extension
    [IsEmbeddedSubmanifold I J S] (hProper : S.IsProperlyEmbedded) (f : C^∞⟮J, S; ℝ⟯) :
    ∃ ftilde : C^∞⟮I, M; ℝ⟯, ∀ x : S, ftilde x = f x := by
  classical
  let t : M → Set ℝ := fun x ↦ if hx : x ∈ S then {f ⟨x, hx⟩} else Set.univ
  have ht : ∀ x, Convex ℝ (t x) := by
    intro x
    by_cases hx : x ∈ S
    · simpa [t, hx] using convex_singleton (f ⟨x, hx⟩)
    · simpa [t, hx] using (convex_univ : Convex ℝ (Set.univ : Set ℝ))
  have hloc : ∀ x : M, ∃ W ∈ nhds x, ∃ g : M → ℝ, ContMDiffOn I 𝓘(ℝ) ∞ g W ∧
      ∀ y ∈ W, g y ∈ t y := by
    intro x
    by_cases hxS : x ∈ S
    · let p : S := ⟨x, hxS⟩
      rcases embeddedPointwiseLocalScalarExtension (I := I) (J := J) (S := S) f p with
        ⟨W, hW_open, hxW, g, hg, hg_eq⟩
      refine ⟨W, hW_open.mem_nhds hxW, g, hg, ?_⟩
      intro y hyW
      by_cases hyS : y ∈ S
      · have hyEq : g y = f ⟨y, hyS⟩ := by
          simpa using hg_eq ⟨y, hyS⟩ hyW
        simp [t, hyS, hyEq]
      · simp [t, hyS]
    · let W : Set M := Sᶜ
      let g : M → ℝ := fun _ ↦ 0
      have hWnhds : W ∈ nhds x := hProper.isClosed.isOpen_compl.mem_nhds hxS
      refine ⟨W, hWnhds, g, contMDiffOn_const, ?_⟩
      intro y hyW
      have hyS : y ∉ S := hyW
      simp [t, hyS, g]
  -- Global convex gluing upgrades the pointwise local extensions to one smooth ambient function.
  obtain ⟨ftilde, hftilde⟩ : ∃ ftilde : C^∞⟮I, M; ℝ⟯, ∀ x : M, ftilde x ∈ t x := by
    simpa [t] using
      exists_contMDiffMap_forall_mem_convex_of_local (I := I) (M := M) (F := ℝ) ht hloc
  refine ⟨ftilde, ?_⟩
  intro x
  simpa [t, x.2] using hftilde (x : M)

end
