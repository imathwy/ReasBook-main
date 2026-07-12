import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SmoothManifolds_Lee_2012.Chap01.Sec01_06.Theorem_1_46
import SmoothManifolds_Lee_2012.Chap04.Sec04_21.Definition_4_21_extra_1
import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Theorem_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff
open Manifold

universe uE uE' uH uH' uM uN

section HelperLemmas

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [CompleteSpace E']

/-- Helper for Proposition 4.8: a bijective continuous linear map out of a Banach space is
invertible. -/
lemma ContinuousLinearMap.isInvertible_of_bijective {A : E →L[𝕜] E'}
    (h_inj : Function.Injective A) (h_surj : Function.Surjective A) :
    A.IsInvertible := by
  -- Package the bijection as a continuous linear equivalence.
  let e : E ≃L[𝕜] E' := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.2 h_inj) (LinearMap.range_eq_top.2 h_surj)
  -- The underlying map of a continuous linear equivalence is invertible.
  refine ⟨e, ?_⟩
  simpa [e] using
    (ContinuousLinearEquiv.coe_ofBijective A (LinearMap.ker_eq_bot.2 h_inj)
      (LinearMap.range_eq_top.2 h_surj))

end HelperLemmas

section OwnerLemmas

section RealImmersion

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

namespace IsLocalDiffeomorph

/-- Helper for Proposition 4.8: a smooth local diffeomorphism of finite-dimensional smooth
manifolds is a smooth immersion. -/
theorem isImmersion {F : M → N} (hF : IsLocalDiffeomorph I J ∞ F) :
    IsImmersion I J ∞ F := by
  -- The local diffeomorphism supplies a tangent-space equivalence at every point.
  have hcontMDiff : ContMDiff I J ∞ F := by
    simpa using hF.contMDiff
  refine (Manifold.is_immersion_iff_forall_injective_mfderiv hcontMDiff).2 ?_
  intro p
  -- Rewriting `mfderiv` as that equivalence makes injectivity immediate.
  rw [← hF.mfderivToContinuousLinearEquiv_coe (by simp) p]
  exact (hF.mfderivToContinuousLinearEquiv (by simp) p).injective

end IsLocalDiffeomorph

end RealImmersion

section GenericSubmersion

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {J : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

namespace IsLocalDiffeomorph

/-- Helper for Proposition 4.8: a smooth local diffeomorphism of finite-dimensional smooth
manifolds is a smooth submersion. -/
theorem isSmoothSubmersion {F : M → N} (hF : IsLocalDiffeomorph I J ∞ F) :
    IsSmoothSubmersion I J F := by
  have hcontMDiff : ContMDiff I J ∞ F := by
    simpa using hF.contMDiff
  refine ⟨hcontMDiff, ?_⟩
  intro p
  -- The same tangent-space equivalence also gives surjectivity of the derivative.
  rw [← hF.mfderivToContinuousLinearEquiv_coe (by simp) p]
  exact (hF.mfderivToContinuousLinearEquiv (by simp) p).surjective

end IsLocalDiffeomorph

namespace Manifold.IsSmoothSubmersion

universe uE'' uH'' uP

variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [FiniteDimensional 𝕜 E'']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {K : ModelWithCorners 𝕜 E'' H''}
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

/-- Composing a smooth submersion with a smooth local diffeomorphism on the source yields a smooth
submersion. -/
theorem comp_isLocalDiffeomorph {F : M → N} {G : N → P} (hG : IsSmoothSubmersion J K G)
    (hF : IsLocalDiffeomorph I J ∞ F) : IsSmoothSubmersion I K (G ∘ F) := by
  have hFcontMDiff : ContMDiff I J ∞ F := by
    simpa using hF.contMDiff
  refine ⟨hG.contMDiff.comp hFcontMDiff, ?_⟩
  intro p
  have hmdiffG : MDifferentiableAt J K G (F p) :=
    hG.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmdiffF : MDifferentiableAt I J F p :=
    hFcontMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hmfderiv :
      mfderiv I K (G ∘ F) p = (mfderiv J K G (F p)).comp (mfderiv I J F p) := by
    simpa [Function.comp] using mfderiv_comp p hmdiffG hmdiffF
  rw [hmfderiv]
  intro v
  rcases hG.surjective_mfderiv (F p) v with ⟨w, rfl⟩
  rcases (hF.mfderivToContinuousLinearEquiv (by simp) p).surjective w with ⟨u, rfl⟩
  exact ⟨u, rfl⟩

end Manifold.IsSmoothSubmersion

end GenericSubmersion

end OwnerLemmas

section EqualFinrankOwnerLemmas

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners ℝ E H}
variable {J : ModelWithCorners ℝ E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [BoundarylessManifold I M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

namespace Manifold.IsImmersionAt

/-- Helper for Proposition 4.8: for an equal-dimensional immersion chart, the complementary
normal space has dimension zero. -/
theorem finrank_complement_eq_zero_of_eq_finrank {f : M → N} {p : M}
    (hp : IsImmersionAt I J ∞ f p)
    (h_dim : Module.finrank ℝ E = Module.finrank ℝ E') :
    Module.finrank ℝ hp.complement = 0 := by
  have hinj_comp :
      Function.Injective
        ((hp.equiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ E hp.complement)).toLinearMap) := by
    intro x y hxy
    have hxy' :
        ContinuousLinearMap.inr ℝ E hp.complement x =
          ContinuousLinearMap.inr ℝ E hp.complement y := hp.equiv.injective hxy
    simpa using congrArg Prod.snd hxy'
  letI : FiniteDimensional ℝ hp.complement :=
    FiniteDimensional.of_injective
      ((hp.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E hp.complement)).toLinearMap)
      hinj_comp
  -- Compare the product-model dimension with the codomain dimension through the immersion witness.
  have hprod : Module.finrank ℝ (E × hp.complement) = Module.finrank ℝ E' := by
    simpa using hp.equiv.toLinearEquiv.finrank_eq
  -- Equal ambient dimensions force the complementary factor to have zero finrank.
  rw [Module.finrank_prod, h_dim] at hprod
  omega

/-- Helper for Proposition 4.8: in equal dimension, the immersion chart normal form collapses to a
genuine linear equivalence between the model spaces. -/
theorem exists_chart_linear_equiv_of_eq_finrank {f : M → N} {p : M}
    (hp : IsImmersionAt I J ∞ f p)
    (h_dim : Module.finrank ℝ E = Module.finrank ℝ E') :
    ∃ e0 : E ≃L[ℝ] E',
      Set.EqOn (((hp.codChart.extend J) ∘ f ∘ (hp.domChart.extend I).symm)) e0
        ((hp.domChart.extend I).target) ∧
      e0 '' ((hp.domChart.extend I).target) ⊆ (hp.codChart.extend J).target := by
  have hinj_comp :
      Function.Injective
        ((hp.equiv.toContinuousLinearMap.comp
          (ContinuousLinearMap.inr ℝ E hp.complement)).toLinearMap) := by
    intro x y hxy
    have hxy' :
        ContinuousLinearMap.inr ℝ E hp.complement x =
          ContinuousLinearMap.inr ℝ E hp.complement y := hp.equiv.injective hxy
    simpa using congrArg Prod.snd hxy'
  letI : FiniteDimensional ℝ hp.complement :=
    FiniteDimensional.of_injective
      ((hp.equiv.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ E hp.complement)).toLinearMap)
      hinj_comp
  have hsubsingleton : Subsingleton hp.complement := by
    exact (Module.finrank_zero_iff).1 (hp.finrank_complement_eq_zero_of_eq_finrank h_dim)
  letI : Subsingleton hp.complement := hsubsingleton
  letI : Unique hp.complement :=
    { default := 0
      uniq := fun x => Subsingleton.elim x 0 }
  let e0 : E ≃L[ℝ] E' :=
    (ContinuousLinearEquiv.prodUnique ℝ E hp.complement).symm.trans hp.equiv
  have hEq0 :
      Set.EqOn (((hp.codChart.extend J) ∘ f ∘ (hp.domChart.extend I).symm)) e0
        ((hp.domChart.extend I).target) := by
    -- Once the complement is trivial, the immersion normal form is literally a linear equivalence.
    intro x hx
    have hzero : (0 : hp.complement) = default := Subsingleton.elim _ _
    simpa [e0, Function.comp, hzero] using hp.writtenInCharts hx
  refine ⟨e0, hEq0, ?_⟩
  · -- Rewriting through the chart equation reduces the target control to the immersion API lemma.
    rintro y ⟨x, hx, rfl⟩
    have hmem : hp.equiv (x, 0) ∈ (hp.codChart.extend J).target :=
      hp.map_target_subset_target ⟨x, hx, rfl⟩
    have he0 : e0 x = hp.equiv (x, 0) := by
      calc
        e0 x = (((hp.codChart.extend J) ∘ f ∘ (hp.domChart.extend I).symm) x) := (hEq0 hx).symm
        _ = hp.equiv (x, 0) := hp.writtenInCharts hx
    exact he0.symm ▸ hmem

end Manifold.IsImmersionAt

/-- Helper for Proposition 4.8: a model-space partial diffeomorphism written in arbitrary maximal
atlas extended charts transports back to a manifold partial diffeomorphism. -/
lemma partialDiffeomorph_of_writtenInExtend
    {f : M → N} {p : M}
    {domChart : OpenPartialHomeomorph M H} {codChart : OpenPartialHomeomorph N H'}
    (hpDom : p ∈ domChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I ∞ M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J ∞ N)
    {Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') E E' ∞}
    (hpΨ : domChart.extend I p ∈ Ψ.source)
    (hsource :
      Ψ.source ⊆
        (domChart.extend I).target ∩
          (f ∘ (domChart.extend I).symm) ⁻¹' (codChart.extend J).source)
    (htarget : Ψ.target ⊆ (codChart.extend J).target)
    (hEq : Set.EqOn (((codChart.extend J) ∘ f ∘ (domChart.extend I).symm)) Ψ Ψ.source) :
    ∃ Φ : PartialDiffeomorph I J M N ∞, p ∈ Φ.source ∧ Set.EqOn f Φ Φ.source := by
  let Γ : PartialEquiv M N :=
    (domChart.extend I).trans (Ψ.toPartialEquiv.trans (codChart.extend J).symm)
  have hinner_source :
      (Ψ.toPartialEquiv.trans (codChart.extend J).symm).source = Ψ.source := by
    ext y
    constructor
    · intro hy
      simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
        Set.mem_preimage] at hy
      exact hy.1
    · intro hy
      have hy_target : Ψ y ∈ Ψ.target := Ψ.map_source hy
      simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, Set.mem_inter_iff,
        Set.mem_preimage]
      exact ⟨hy, htarget hy_target⟩
  have hΓ_source :
      Γ.source = (domChart.extend I).source ∩ (domChart.extend I) ⁻¹' Ψ.source := by
    change
      ((domChart.extend I).trans (Ψ.toPartialEquiv.trans (codChart.extend J).symm)).source =
        (domChart.extend I).source ∩ (domChart.extend I) ⁻¹' Ψ.source
    rw [PartialEquiv.trans_source, hinner_source]
  have hinner_target :
      (Ψ.toPartialEquiv.trans (codChart.extend J).symm).target =
        (codChart.extend J).source ∩
          (codChart.extend J) ⁻¹' Ψ.target := by
    rw [PartialEquiv.trans_target]
    rfl
  have hΓ_target :
      Γ.target =
        (codChart.extend J).source ∩
          (codChart.extend J) ⁻¹' Ψ.target := by
    calc
      Γ.target = (Ψ.toPartialEquiv.trans (codChart.extend J).symm).target := by
        ext y
        constructor
        · intro hy
          simp only [Γ, PartialEquiv.trans_target, Set.mem_inter_iff, Set.mem_preimage] at hy
          exact hy.1
        · intro hy
          have hy_source :
              (Ψ.toPartialEquiv.trans (codChart.extend J).symm).symm y ∈
                (Ψ.toPartialEquiv.trans (codChart.extend J).symm).source :=
            (Ψ.toPartialEquiv.trans (codChart.extend J).symm).map_target hy
          have hy_Ψ_source :
              (Ψ.toPartialEquiv.trans (codChart.extend J).symm).symm y ∈ Ψ.source := by
            rwa [hinner_source] at hy_source
          have hy_chart :
              (Ψ.toPartialEquiv.trans (codChart.extend J).symm).symm y ∈
                (domChart.extend I).target := (hsource hy_Ψ_source).1
          simp only [Γ, PartialEquiv.trans_target, Set.mem_inter_iff, Set.mem_preimage]
          exact ⟨hy, hy_chart⟩
      _ = (codChart.extend J).source ∩ (codChart.extend J) ⁻¹' Ψ.target := hinner_target
  have hcodChart_symm :
      ContMDiffOn 𝓘(ℝ, E') J ∞ (codChart.extend J).symm (codChart.extend J).target := by
    -- Rewrite the standard atlas smoothness lemma onto the concrete extended-chart target.
    convert contMDiffOn_extend_symm (I := J) (n := (∞ : ℕ∞ω)) hcodChart using 2
    simpa [Set.inter_comm] using (J.image_eq codChart.target).symm
  have hmid_to :
      ContMDiffOn 𝓘(ℝ, E) J ∞ ((codChart.extend J).symm ∘ Ψ) Ψ.source := by
    -- Compose the model partial diffeomorphism with the inverse target chart.
    refine hcodChart_symm.comp Ψ.contMDiffOn_toFun ?_
    intro x hx
    exact htarget (Ψ.map_source hx)
  have hdomChart_symm :
      ContMDiffOn 𝓘(ℝ, E) I ∞ (domChart.extend I).symm (domChart.extend I).target := by
    -- The same rewrite gives smoothness of the inverse source chart on its target.
    convert contMDiffOn_extend_symm (I := I) (n := (∞ : ℕ∞ω)) hdomChart using 2
    simpa [Set.inter_comm] using (I.image_eq domChart.target).symm
  have hmid_inv :
      ContMDiffOn 𝓘(ℝ, E') I ∞ ((domChart.extend I).symm ∘ Ψ.symm) Ψ.target := by
    -- The inverse branch lands back in the source chart target by the source inclusion hypothesis.
    refine hdomChart_symm.comp Ψ.contMDiffOn_invFun ?_
    intro y hy
    exact (hsource (Ψ.map_target hy)).1
  let Φ : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := Γ
      open_source := by
        rw [hΓ_source]
        exact (domChart.continuousOn_extend (I := I)).isOpen_inter_preimage
          domChart.isOpen_extend_source Ψ.open_source
      open_target := by
        rw [hΓ_target]
        exact (codChart.continuousOn_extend (I := J)).isOpen_inter_preimage
          codChart.isOpen_extend_source Ψ.open_target
      contMDiffOn_toFun := by
        -- Compose the source chart with the model branch and then with the inverse target chart.
        rw [hΓ_source]
        simpa [Γ, Function.comp_assoc] using
          hmid_to.comp' (contMDiffOn_extend (I := I) (n := (∞ : ℕ∞ω)) hdomChart)
      contMDiffOn_invFun := by
        -- Apply the same chart-composition argument to the inverse branch.
        rw [hΓ_target]
        simpa [Γ, Function.comp_assoc] using
          hmid_inv.comp' (contMDiffOn_extend (I := J) (n := (∞ : ℕ∞ω)) hcodChart) }
  refine ⟨Φ, ?_, ?_⟩
  · -- The base point belongs to the transported source because its source-chart image lies in `Ψ`.
    rw [show Φ.source = Γ.source by rfl, hΓ_source]
    exact ⟨by simpa [OpenPartialHomeomorph.extend_source] using hpDom, hpΨ⟩
  · intro x hx
    have hx' : x ∈ (domChart.extend I).source ∩ (domChart.extend I) ⁻¹' Ψ.source := by
      simpa [Φ, hΓ_source] using hx
    have hxΨ : domChart.extend I x ∈ Ψ.source := hx'.2
    have hx_left : (domChart.extend I).symm (domChart.extend I x) = x :=
      (domChart.extend I).left_inv hx'.1
    have hfx_source : f x ∈ (codChart.extend J).source := by
      have hpre : f ((domChart.extend I).symm (domChart.extend I x)) ∈
          (codChart.extend J).source := by
        simpa [Function.comp] using (hsource hxΨ).2
      exact (congrArg f hx_left) ▸ hpre
    -- On the transported source, the chart representative agrees with `Ψ`, so the charts cancel.
    have hΦx : Φ x = f x := by
      calc
        Φ x = (codChart.extend J).symm (Ψ (domChart.extend I x)) := by
          simp [Φ, Γ, PartialEquiv.trans_apply]
        _ = (codChart.extend J).symm
              ((((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (domChart.extend I x))) := by
          rw [(hEq hxΨ).symm]
        _ = f x := by
          rw [show (((codChart.extend J) ∘ f ∘ (domChart.extend I).symm) (domChart.extend I x)) =
              (codChart.extend J) (f x) by
                change (codChart.extend J) (f ((domChart.extend I).symm (domChart.extend I x))) =
                  (codChart.extend J) (f x)
                exact congrArg (codChart.extend J) (congrArg f hx_left)]
          exact (codChart.extend J).left_inv hfx_source
    exact hΦx.symm

/-- Helper for Proposition 4.8: transporting a model-space partial diffeomorphism through
maximal-atlas extended charts yields a local diffeomorphism at the manifold point. -/
lemma isLocalDiffeomorphAt_of_writtenInExtend
    {f : M → N} {p : M}
    {domChart : OpenPartialHomeomorph M H} {codChart : OpenPartialHomeomorph N H'}
    (hpDom : p ∈ domChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I ∞ M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J ∞ N)
    {Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') E E' ∞}
    (hpΨ : domChart.extend I p ∈ Ψ.source)
    (hsource :
      Ψ.source ⊆
        (domChart.extend I).target ∩
          (f ∘ (domChart.extend I).symm) ⁻¹' (codChart.extend J).source)
    (htarget : Ψ.target ⊆ (codChart.extend J).target)
    (hEq : Set.EqOn (((codChart.extend J) ∘ f ∘ (domChart.extend I).symm)) Ψ Ψ.source) :
    IsLocalDiffeomorphAt I J ∞ f p := by
  -- Once the transported partial diffeomorphism exists, it is exactly the local witness we need.
  obtain ⟨Φ, hpΦ, hΦ⟩ :=
    partialDiffeomorph_of_writtenInExtend
      (I := I) (J := J) (f := f) (p := p) (domChart := domChart) (codChart := codChart)
      hpDom hdomChart hcodChart hpΨ hsource htarget hEq
  exact ⟨Φ, hpΦ, hΦ⟩

/-- Helper for Proposition 4.8: if an immersion chart representative is literally a linear
equivalence on the domain chart target, then the map is a local diffeomorphism at the base point. -/
lemma isLocalDiffeomorphAt_of_chart_eq_continuousLinearEquiv
    {f : M → N} {p : M}
    {domChart : OpenPartialHomeomorph M H} {codChart : OpenPartialHomeomorph N H'}
    (hpDom : p ∈ domChart.source)
    (hdomChart : domChart ∈ IsManifold.maximalAtlas I ∞ M)
    (hcodChart : codChart ∈ IsManifold.maximalAtlas J ∞ N)
    (hsourceChart : domChart.source ⊆ f ⁻¹' codChart.source)
    {e0 : E ≃L[ℝ] E'}
    (hEq : Set.EqOn (((codChart.extend J) ∘ f ∘ (domChart.extend I).symm)) e0
      ((domChart.extend I).target))
    (htarget : e0 '' ((domChart.extend I).target) ⊆ (codChart.extend J).target) :
    IsLocalDiffeomorphAt I J ∞ f p := by
  let s : Set E := interior ((domChart.extend I).target)
  have hs_open : IsOpen s := isOpen_interior
  have hpInt : domChart.extend I p ∈ s := by
    -- Boundarylessness turns every point into an interior point in any maximal-atlas chart.
    exact (I.isInteriorPoint_iff_of_mem_maximalAtlas
      (n := (∞ : ℕ∞ω)) (hn := by simp) hdomChart hpDom).1 BoundarylessManifold.isInteriorPoint
  let R : OpenPartialHomeomorph E E' := e0.toHomeomorph.toOpenPartialHomeomorph
  have hsource_restr : (R.restr s).source = s := by
    rw [R.restr_source' s hs_open]
    exact Set.inter_eq_right.mpr (by intro x hx; simpa [R] using hx)
  have htarget_restr : (R.restr s).target = e0 '' s := by
    rw [← (R.restr s).image_source_eq_target, hsource_restr]
    simp [R]
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E') E E' ∞ :=
    { toPartialEquiv := (R.restr s).toPartialEquiv
      open_source := (R.restr s).open_source
      open_target := (R.restr s).open_target
      contMDiffOn_toFun := by
        -- The restricted forward branch is still the linear diffeomorphism `e0`.
        rw [hsource_restr]
        simpa [R] using e0.contDiff.contMDiff.contMDiffOn
      contMDiffOn_invFun := by
        -- The restricted inverse branch is still the inverse linear diffeomorphism.
        rw [htarget_restr]
        simpa [R] using e0.symm.contDiff.contMDiff.contMDiffOn }
  have hΨ_source : Ψ.source = s := by
    simpa [Ψ] using hsource_restr
  have hΨ_target : Ψ.target = e0 '' s := by
    simpa [Ψ] using htarget_restr
  -- Route correction: after collapsing the immersion normal form to `e0`, reuse the chart-transport
  -- packaging from Theorem 4.5 instead of rebuilding a local inverse directly on the manifold.
  refine isLocalDiffeomorphAt_of_writtenInExtend
    (I := I) (J := J) (f := f) (p := p) (domChart := domChart) (codChart := codChart)
    hpDom hdomChart hcodChart (Ψ := Ψ) ?_ ?_ ?_ ?_
  · -- The base point lies in the restricted model source because it is an interior chart point.
    rw [hΨ_source]
    exact hpInt
  · intro x hx
    rw [hΨ_source] at hx
    refine ⟨interior_subset hx, ?_⟩
    have hx_source_ext : (domChart.extend I).symm x ∈ (domChart.extend I).source :=
      (domChart.extend I).map_target (interior_subset hx)
    have hx_source : (domChart.extend I).symm x ∈ domChart.source := by
      simpa [OpenPartialHomeomorph.extend_source] using hx_source_ext
    simpa [OpenPartialHomeomorph.extend_source] using hsourceChart hx_source
  · intro y hy
    rw [hΨ_target] at hy
    exact htarget ((Set.image_mono interior_subset) hy)
  · intro x hx
    -- On the restricted source, `Ψ` is definitionally the same forward map as `e0`.
    rw [hΨ_source] at hx
    simpa [Ψ, R] using hEq (interior_subset hx)

namespace Manifold.IsImmersion

/-- Helper for Proposition 4.8: on a boundaryless smooth manifold, an equal-dimensional immersion
is already a local diffeomorphism because its chart normal form has zero-dimensional normal
complement. -/
theorem isLocalDiffeomorph_of_eq_finrank {F : M → N} (hF : IsImmersion I J ∞ F)
    (h_dim : Module.finrank ℝ E = Module.finrank ℝ E') :
    IsLocalDiffeomorph I J ∞ F := by
  intro p
  let hp := hF.isImmersionAt p
  -- Route correction: follow the source chart-normal-form proof instead of the blocked derivative
  -- API route. Equal dimensions force the immersion complement to vanish.
  obtain ⟨e0, hEq, htarget⟩ := hp.exists_chart_linear_equiv_of_eq_finrank h_dim
  -- The straightened chart representative is literally a linear equivalence, so it transports to a
  -- local diffeomorphism at `p`.
  exact isLocalDiffeomorphAt_of_chart_eq_continuousLinearEquiv
    (domChart := hp.domChart) (codChart := hp.codChart) hp.mem_domChart_source
    hp.domChart_mem_maximalAtlas hp.codChart_mem_maximalAtlas hp.source_subset_preimage_source
    hEq htarget

end Manifold.IsImmersion

namespace Manifold.IsSmoothSubmersion

/-- Helper for Proposition 4.8: on a boundaryless smooth manifold, an equal-dimensional smooth
submersion is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_eq_finrank {F : M → N}
    (hF : IsSmoothSubmersion I J F) (h_dim : Module.finrank ℝ E = Module.finrank ℝ E') :
    IsLocalDiffeomorph I J ∞ F := by
  intro p
  letI : NormedAddCommGroup (TangentSpace I p) := by
    change NormedAddCommGroup E
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I p) := by
    change NormedSpace ℝ E
    infer_instance
  letI : CompleteSpace (TangentSpace I p) := by
    change CompleteSpace E
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace I p) := by
    change FiniteDimensional ℝ E
    infer_instance
  letI : NormedAddCommGroup (TangentSpace J (F p)) := by
    change NormedAddCommGroup E'
    infer_instance
  letI : NormedSpace ℝ (TangentSpace J (F p)) := by
    change NormedSpace ℝ E'
    infer_instance
  letI : CompleteSpace (TangentSpace J (F p)) := by
    change CompleteSpace E'
    infer_instance
  letI : FiniteDimensional ℝ (TangentSpace J (F p)) := by
    change FiniteDimensional ℝ E'
    infer_instance
  have h_dim_tangent :
      Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ (TangentSpace J (F p)) := by
    simpa using h_dim
  have hsurj : Function.Surjective (mfderiv I J F p) :=
    hF.surjective_mfderiv p
  have hinj : Function.Injective (mfderiv I J F p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h_dim_tangent).mpr hsurj
  have hInv : (mfderiv I J F p).IsInvertible :=
    by
      let e : TangentSpace I p ≃L[ℝ] TangentSpace J (F p) :=
        ContinuousLinearEquiv.ofBijective (mfderiv I J F p) (LinearMap.ker_eq_bot.2 hinj)
          (LinearMap.range_eq_top.2 hsurj)
      refine ⟨e, ?_⟩
      simpa [e] using
        (ContinuousLinearEquiv.coe_ofBijective (mfderiv I J F p)
          (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj))
  -- The inverse function theorem applies because boundaryless manifolds have no boundary points.
  exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    (I := I) (J := J) (n := ∞) (by simp) BoundarylessManifold.isInteriorPoint hF.contMDiff hInv

end Manifold.IsSmoothSubmersion

end EqualFinrankOwnerLemmas

section SourceSpecialization

variable {m n : ℕ}
variable {M : Type uM} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin m))) ∞ M]
variable {N : Type uN} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ N]

local notation "I_m" => 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
local notation "I_n" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

/-- Proposition 4.8 (1): a map between smooth manifolds without boundary is a local
diffeomorphism if and only if it is both a smooth immersion and a smooth submersion. -/
theorem is_local_diffeomorph_iff_is_immersion_and_is_smooth_submersion {F : M → N} :
    IsLocalDiffeomorph I_m I_n ∞ F ↔
      IsImmersion I_m I_n ∞ F ∧ IsSmoothSubmersion I_m I_n F := by
  refine ⟨fun hF ↦ ⟨hF.isImmersion, hF.isSmoothSubmersion⟩, ?_⟩
  rintro ⟨hFimm, hFsubm⟩
  have hSmooth : ContMDiff I_m I_n ∞ F := hFsubm.contMDiff
  intro p
  letI : NormedAddCommGroup (TangentSpace I_m p) := by
    change NormedAddCommGroup (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I_m p) := by
    change NormedSpace ℝ (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : CompleteSpace (TangentSpace I_m p) := by
    change CompleteSpace (EuclideanSpace ℝ (Fin m))
    infer_instance
  letI : NormedAddCommGroup (TangentSpace I_n (F p)) := by
    change NormedAddCommGroup (EuclideanSpace ℝ (Fin n))
    infer_instance
  letI : NormedSpace ℝ (TangentSpace I_n (F p)) := by
    change NormedSpace ℝ (EuclideanSpace ℝ (Fin n))
    infer_instance
  letI : CompleteSpace (TangentSpace I_n (F p)) := by
    change CompleteSpace (EuclideanSpace ℝ (Fin n))
    infer_instance
  have hinj : Function.Injective (mfderiv I_m I_n F p) :=
    (Manifold.is_immersion_iff_forall_injective_mfderiv hSmooth).mp hFimm p
  have hsurj : Function.Surjective (mfderiv I_m I_n F p) :=
    hFsubm.surjective_mfderiv p
  have hInv : (mfderiv I_m I_n F p).IsInvertible :=
    by
      let e : TangentSpace I_m p ≃L[ℝ] TangentSpace I_n (F p) :=
        ContinuousLinearEquiv.ofBijective (mfderiv I_m I_n F p) (LinearMap.ker_eq_bot.2 hinj)
          (LinearMap.range_eq_top.2 hsurj)
      refine ⟨e, ?_⟩
      simpa [e] using
        (ContinuousLinearEquiv.coe_ofBijective (mfderiv I_m I_n F p)
          (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj))
  -- At Euclidean-model points the source manifold is boundaryless, so the inverse function theorem
  -- upgrades pointwise invertibility of `mfderiv` to a local diffeomorphism.
  exact isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible
    (I := I_m) (J := I_n) (n := ∞) (by simp) BoundarylessManifold.isInteriorPoint hSmooth hInv

/-- Proposition 4.8 (2): if the source and target have the same dimension, then a smooth
immersion is a local diffeomorphism. -/
theorem is_local_diffeomorph_of_is_immersion_of_eq_dim {F : M → N} (hmn : m = n)
    (hF : IsImmersion I_m I_n ∞ F) :
    IsLocalDiffeomorph I_m I_n ∞ F :=
  hF.isLocalDiffeomorph_of_eq_finrank (by
    simpa [finrank_euclideanSpace_fin] using hmn)

/-- Proposition 4.8 (3): if the source and target have the same dimension, then a smooth
submersion is a local diffeomorphism. -/
theorem is_local_diffeomorph_of_is_smooth_submersion_of_eq_dim {F : M → N} (hmn : m = n)
    (hF : IsSmoothSubmersion I_m I_n F) :
    IsLocalDiffeomorph I_m I_n ∞ F :=
  hF.isLocalDiffeomorph_of_eq_finrank (by
    simpa [finrank_euclideanSpace_fin] using hmn)

end SourceSpecialization
