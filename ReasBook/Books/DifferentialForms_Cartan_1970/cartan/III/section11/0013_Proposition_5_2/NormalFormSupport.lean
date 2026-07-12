import Mathlib
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2
import DifferentialForms_Cartan_1970.III.section11.«0010_Definition_III_5_extra_7»
import DifferentialForms_Cartan_1970.III.section11.«0007_Remark_III_5_extra_6»

open Filter
open scoped BigOperators Topology
open MeromorphicOn

noncomputable section

universe u

variable {f : ℂ → ℂ} (L : PeriodPair) (P : Set ℂ)

/-- Helper for Proposition 5.2: the divisor of a meromorphic function on a compact owner has
finite support. -/
lemma divisor_support_finite_of_isCompact
    {K : Set ℂ} {g : ℂ → ℂ} (hK : IsCompact K) :
    (MeromorphicOn.divisor g K).support.Finite := by
  -- Compactness upgrades local finite support of the divisor to ordinary finite support.
  simpa using (MeromorphicOn.divisor g K).finiteSupport hK

/-- Helper for Proposition 5.2: once two parameter integrands agree on a codiscrete subset of the
unit interval, the corresponding curve integrals agree. -/
lemma curveIntegral_eq_of_codiscrete_param_integrand
    {z₀ z₁ : ℂ} (γ : Path z₀ z₁) {φ ψ : ℂ → ℂ}
    (hEq :
      (fun t : ℝ ↦ (((φ dz) (γ.extend t)) (deriv γ.extend t)))
        =ᶠ[Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)]
      (fun t : ℝ ↦ (((ψ dz) (γ.extend t)) (deriv γ.extend t)))) :
    ∫ᶜ z in γ, ((φ dz) z) = ∫ᶜ z in γ, ((ψ dz) z) := by
  -- Rewrite both curve integrals as interval integrals of the parameterized integrands.
  rw [curveIntegral_eq_intervalIntegral_deriv, curveIntegral_eq_intervalIntegral_deriv]
  -- Codiscrete equality on `[0,1]` is enough because interval integrals ignore a codiscrete
  -- subset of the parameter interval.
  exact intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_le_codiscreteWithin measurableSet_uIoc hEq)

/-- Helper for Proposition 5.2: codiscrete agreement on an open owner transfers
curve-integrability across a nondegenerate affine segment whose image stays inside that owner. -/
lemma curveIntegrable_segment_of_codiscreteWithin
    {φ ψ : ℂ → ℂ} {U : Set ℂ} {a b : ℂ} (hne : a ≠ b)
    (hRange : Set.range (Path.segment a b) ⊆ U)
    (hEq : φ =ᶠ[Filter.codiscreteWithin U] ψ)
    (hψ : CurveIntegrable (fun z ↦ (ψ dz) z) (Path.segment a b)) :
    CurveIntegrable (fun z ↦ (φ dz) z) (Path.segment a b) := by
  let A : Set ℂ := {z | φ z = ψ z}
  have hA_U : A ∈ Filter.codiscreteWithin U := by
    -- Repackage codiscrete equality as a codiscrete good set of owner points.
    simpa [A, Filter.EventuallyEq] using hEq
  have hA_range : A ∈ Filter.codiscreteWithin (Set.range (Path.segment a b)) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA_U ⊢
    intro z hz
    have hzU : z ∈ U := hRange hz
    -- Restrict the ambient codiscrete equality to the compact segment image.
    refine Filter.mem_of_superset (hA_U z hzU) ?_
    intro w hw
    rcases hw with hwA | hwUc
    · exact Or.inl hwA
    · exact Or.inr fun hwRange ↦ hwUc (hRange hwRange)
  have hBadImage : (Set.range (Path.segment a b) \ A).Finite := by
    -- Compactness of the segment image makes the bad image set finite.
    exact (isCompact_range (Path.segment a b).continuous).finite_diff_of_mem_codiscreteWithin
      hA_range
  have hline_injective :
      Function.Injective (fun t : Set.uIoc (0 : ℝ) 1 ↦ AffineMap.lineMap a b (t : ℝ)) := by
    intro s t hst
    apply Subtype.ext
    rcases (AffineMap.lineMap_eq_lineMap_iff (p₀ := a) (p₁ := b) (c₁ := (s : ℝ))
      (c₂ := (t : ℝ))).mp hst with hab | hst'
    · exact (hne hab).elim
    · exact hst'
  let B : Set ℝ :=
    {t | t ∈ Set.uIoc (0 : ℝ) 1 ∧
      AffineMap.lineMap a b t ∈ Set.range (Path.segment a b) \ A}
  have hBadParamSubtype :
      {t : Set.uIoc (0 : ℝ) 1 |
          AffineMap.lineMap a b (t : ℝ) ∈ Set.range (Path.segment a b) \ A}.Finite := by
    -- Injectivity of the affine segment parameterization keeps the bad parameter set finite.
    exact hBadImage.preimage hline_injective.injOn
  have hBadParam : B.Finite := by
    have hImage :
        (Subtype.val '' {t : Set.uIoc (0 : ℝ) 1 |
          AffineMap.lineMap a b (t : ℝ) ∈ Set.range (Path.segment a b) \ A}).Finite := by
      exact hBadParamSubtype.image Subtype.val
    convert hImage using 1
    ext t
    constructor
    · intro ht
      refine ⟨⟨t, ht.1⟩, ?_, rfl⟩
      simpa [B] using ht.2
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.2, by simpa [B] using ht⟩
  have hParamEq :
      (fun t : ℝ ↦ ((φ dz) (AffineMap.lineMap a b t)) (b - a))
        =ᶠ[Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)]
      (fun t : ℝ ↦ ((ψ dz) (AffineMap.lineMap a b t)) (b - a)) := by
    change
      {t : ℝ |
          ((φ dz) (AffineMap.lineMap a b t)) (b - a) =
            ((ψ dz) (AffineMap.lineMap a b t)) (b - a)} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    have hBadParam_cod :
        ({t : ℝ | t ∉ B} : Set ℝ) ∈
          Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1) :=
      compl_finite_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) 1) hBadParam
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hBadParam_cod
    intro t ht
    -- Away from the finite bad parameter set, the two scalar coefficients agree on the segment.
    refine Filter.mem_of_superset (hBadParam_cod t ht) ?_
    intro u hu
    rcases hu with huNotB | huOutside
    · by_cases huI : u ∈ Set.uIoc (0 : ℝ) 1
      · have huRange : AffineMap.lineMap a b u ∈ Set.range (Path.segment a b) := by
          have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
            simpa using (show u ∈ Set.Icc (min (0 : ℝ) 1) (max (0 : ℝ) 1) from
              ⟨le_of_lt huI.1, huI.2⟩)
          refine ⟨⟨u, huIcc⟩, ?_⟩
          simp [Path.segment, AffineMap.lineMap_apply]
        have huA : AffineMap.lineMap a b u ∈ A := by
          by_contra huA
          exact huNotB ⟨huI, ⟨huRange, huA⟩⟩
        have huEq : φ (AffineMap.lineMap a b u) = ψ (AffineMap.lineMap a b u) := by
          simpa [A] using huA
        exact Or.inl (by simp [huEq])
      · exact Or.inr huI
    · exact Or.inr huOutside
  -- Rewrite segment integrability to the parameter interval and transfer it across the
  -- codiscrete parameter agreement.
  rw [curveIntegrable_segment] at hψ ⊢
  exact (intervalIntegrable_congr_codiscreteWithin hParamEq).mpr hψ

/-- Helper for Proposition 5.2: on `Set.uIoc (0,1]`, a single oriented-boundary component is
injective, so the preimage of a finite bad image set is finite there. -/
lemma boundary_component_finite_preimage_uIoc
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (i : ι) {E : Set ℂ} (hE : E.Finite) :
    (((Γ i).toPath.extend ⁻¹' E) ∩ Set.uIoc (0 : ℝ) 1).Finite := by
  let F : Set.uIoc (0 : ℝ) 1 → ℂ := fun t ↦ (Γ i).toPath.extend t
  have hF_inj : Function.Injective F := by
    intro s t hst
    have hsU : (s : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using s.2
    have htU : (t : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa using t.2
    have hsI : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨hsU.1.le, hsU.2⟩
    have htI : (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨htU.1.le, htU.2⟩
    have hPath :
        (Γ i).toPath ⟨(s : ℝ), hsI⟩ = (Γ i).toPath ⟨(t : ℝ), htI⟩ := by
      simpa [F, Path.extend_apply (γ := (Γ i).toPath) hsI,
        Path.extend_apply (γ := (Γ i).toPath) htI] using hst
    rcases hΓ.simple_loops i hPath with hEq | hEnds | hEnds
    · cases s
      cases t
      cases hEq
      rfl
    · have hs0 : (s : ℝ) = 0 := by
        exact congrArg Subtype.val (congrArg Prod.fst hEnds)
      exfalso
      linarith [hsU.1, hs0]
    · have ht0 : (t : ℝ) = 0 := by
        exact congrArg Subtype.val (congrArg Prod.snd hEnds)
      exfalso
      linarith [htU.1, ht0]
  have hSubtype :
      {t : Set.uIoc (0 : ℝ) 1 | F t ∈ E}.Finite := by
    exact hE.preimage hF_inj.injOn
  have hImage :
      (Subtype.val '' {t : Set.uIoc (0 : ℝ) 1 | F t ∈ E}).Finite := by
    exact hSubtype.image Subtype.val
  -- Forgetting the subtype identifies the finite subtype preimage with the desired parameter set.
  convert hImage using 1
  ext t
  constructor
  · intro ht
    refine ⟨⟨t, ht.2⟩, ?_, rfl⟩
    simpa [F] using ht.1
  · rintro ⟨t, ht, rfl⟩
    exact ⟨by simpa [F] using ht, t.2⟩

/-- Helper for Proposition 5.2: a finite support set inside `interior K` admits a positive radius
around each chosen point that stays in `interior K` and avoids the other support points. -/
lemma exists_separating_radius_closedBall_subset_interior
    {K : Set ℂ} {s : Finset ℂ} {z : ℂ} (hz : z ∈ s)
    (hsK : (↑s : Set ℂ) ⊆ interior K) :
    ∃ r > 0,
      Metric.closedBall z r ⊆ interior K ∧
        ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z r := by
  have hzK : z ∈ interior K := hsK (by simpa using hz)
  rcases Metric.mem_nhds_iff.1 (isOpen_interior.mem_nhds hzK) with ⟨R, hR, hRsub⟩
  let t : Set ℂ := (↑s : Set ℂ) \ ({z} : Set ℂ)
  have htfinite : t.Finite := s.finite_toSet.subset (by
    intro w hw
    exact hw.1)
  have htclosed : IsClosed t := htfinite.isClosed
  have hz_not_closure_t : z ∉ closure t := by
    simp [t, htclosed.closure_eq]
  obtain ⟨ε, hε, hεlt⟩ := Metric.exists_real_pos_lt_infEDist_of_notMem_closure hz_not_closure_t
  let r : ℝ := min (R / 2) ε
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min (half_pos hR) hε
  have hrR : r < R := by
    have hhalf : R / 2 < R := by linarith
    exact lt_of_le_of_lt (by exact min_le_left _ _) hhalf
  have hrε : r ≤ ε := by
    dsimp [r]
    exact min_le_right _ _
  refine ⟨r, hr, ?_, ?_⟩
  · -- The interior neighborhood ball contains the smaller closed ball.
    exact (Metric.closedBall_subset_ball hrR).trans hRsub
  · -- Any other support point in the closed ball would contradict the `infEDist` separation.
    intro w hw hwz hwball
    have hwt : w ∈ t := by
      refine ⟨by simpa using hw, ?_⟩
      simpa [Set.mem_singleton_iff] using hwz
    have hInf : Metric.infEDist z t ≤ edist z w := Metric.infEDist_le_edist_of_mem hwt
    have hdist : dist z w ≤ ε := by
      have hdist_r : dist z w ≤ r := by
        simpa [Metric.mem_closedBall, dist_comm] using hwball
      exact hdist_r.trans hrε
    have hedist : edist z w ≤ ENNReal.ofReal ε := by
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal hdist
    exact (not_lt_of_ge hedist) (lt_of_lt_of_le hεlt hInf)

/-- Helper for Proposition 5.2: global punctured differentiability away from a finite support set
restricts to any small punctured ball that avoids the rest of the support. -/
lemma differentiableOn_punctured_ball_of_finite_support_separation
    {D : Set ℂ} {s : Finset ℂ} {f : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hD : Metric.closedBall z r ⊆ D)
    (hsep : ∀ w ∈ s, w ≠ z → w ∉ Metric.closedBall z r)
    (hhol : DifferentiableOn ℂ f (D \ (↑s : Set ℂ))) :
    DifferentiableOn ℂ f (Metric.ball z r \ ({z} : Set ℂ)) := by
  -- Restrict the global punctured differentiability to the chosen small punctured ball.
  refine hhol.mono ?_
  intro w hw
  refine ⟨hD (Metric.ball_subset_closedBall hw.1), ?_⟩
  intro hwS
  by_cases hwz : w = z
  · exact hw.2 hwz
  · exact hsep w hwS hwz (Metric.ball_subset_closedBall hw.1)

/-- Helper for Proposition 5.2: if the divisor vanishes on `frontier K`, then every support point
of the compact-owner divisor lies in `interior K`. -/
lemma divisor_support_subset_interior_of_frontier_zero
    {K : Set ℂ} {g : ℂ → ℂ} (hK : IsCompact K)
    (hfrontier_zero : ∀ z ∈ frontier K, MeromorphicOn.divisor g K z = 0) :
    let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
    (↑s : Set ℂ) ⊆ interior K := by
  classical
  let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
  change (↑s : Set ℂ) ⊆ interior K
  intro z hz
  have hz_support : z ∈ (MeromorphicOn.divisor g K).support := by
    simpa [s] using hz
  have hzK : z ∈ K := by
    -- Outside `K`, the divisor is definitionally zero, so support points must lie in `K`.
    by_contra hzK
    rw [Function.mem_support] at hz_support
    simp [hzK] at hz_support
  by_contra hzInterior
  have hz_frontier : z ∈ frontier K := by
    exact (mem_frontier_iff_notMem_interior hzK).2 hzInterior
  have hz_zero : MeromorphicOn.divisor g K z = 0 := hfrontier_zero z hz_frontier
  rw [Function.mem_support] at hz_support
  exact hz_support hz_zero

/-- Helper for Proposition 5.2: if a finite set lies in `interior K`, every boundary component of
an oriented boundary of `K` is disjoint from that set. -/
lemma boundary_path_disjoint_of_finset_subset_interior
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) {s : Finset ℂ}
    (hsK : (↑s : Set ℂ) ⊆ interior K) :
    ∀ i, Disjoint (Set.range ⇑(Γ i).toPath) (↑s : Set ℂ) := by
  intro i
  refine Set.disjoint_left.2 ?_
  intro z hzRange hzS
  have hzFrontier : z ∈ frontier K := hΓ.range_toPath_subset_frontier i hzRange
  have hzInterior : z ∈ interior K := hsK hzS
  exact (Set.disjoint_left.1 disjoint_interior_frontier hzInterior hzFrontier)

/-- Helper for Proposition 5.2: frontier divisor vanishing implies every oriented-boundary
component is disjoint from the compact-owner divisor support finset. -/
lemma boundary_path_disjoint_of_divisor_frontier_zero
    {ι : Type u} [Fintype ι] {K : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) {g : ℂ → ℂ}
    (hfrontier_zero : ∀ z ∈ frontier K, MeromorphicOn.divisor g K z = 0) :
    let s : Finset ℂ :=
      (divisor_support_finite_of_isCompact (K := K) (g := g) hΓ.isCompact).toFinset
    ∀ i,
      Disjoint
        (Set.range ⇑(Γ i).toPath)
        (↑s : Set ℂ) := by
  classical
  let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hΓ.isCompact).toFinset
  change ∀ i, Disjoint (Set.range ⇑(Γ i).toPath) (↑s : Set ℂ)
  have hsK :
      (↑s : Set ℂ) ⊆ interior K := by
    simpa [s] using divisor_support_subset_interior_of_frontier_zero
      (K := K) (g := g) hΓ.isCompact hfrontier_zero
  simpa using
    (boundary_path_disjoint_of_finset_subset_interior
      (K := K) (Γ := Γ) hΓ (s := s) hsK)

/-- Helper for Proposition 5.2: a compact owner `K ⊆ D` admits an open owner `U` whose divisor
agrees with the divisor on `K` up to the original compact support finset. -/
lemma exists_open_owner_with_divisor_zero_off_support
    {D K : Set ℂ} {g : ℂ → ℂ}
    (hg : MeromorphicOn g D) (hD_open : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    let s : Finset ℂ := (divisor_support_finite_of_isCompact (K := K) (g := g) hK).toFinset
    ∃ U, IsOpen U ∧ K ⊆ U ∧ U ⊆ D ∧
      ∀ z, z ∈ U → z ∉ (↑s : Set ℂ) → MeromorphicOn.divisor g U z = 0 := by
  classical
  let hsupportK :=
    divisor_support_finite_of_isCompact (K := K) (g := g) hK
  let s : Finset ℂ := hsupportK.toFinset
  obtain ⟨ε, hε, hεD⟩ := hK.exists_cthickening_subset_open hD_open hKD
  let L' : Set ℂ := Metric.cthickening ε K
  let V : Set ℂ := Metric.thickening ε K
  have hLcompact : IsCompact L' := by
    simpa [L'] using hK.cthickening
  have hKL : K ⊆ L' := by
    simpa [L'] using Metric.self_subset_cthickening K
  have hKV : K ⊆ V := by
    simpa [V] using Metric.self_subset_thickening hε K
  have hVL : V ⊆ L' := by
    simpa [V, L'] using Metric.thickening_subset_cthickening ε K
  have hLD : L' ⊆ D := by
    simpa [L'] using hεD
  have hgL : MeromorphicOn g L' := hg.mono_set hLD
  let hsupportL :=
    divisor_support_finite_of_isCompact (K := L') (g := g) hLcompact
  let t : Finset ℂ := hsupportL.toFinset \ s
  let U : Set ℂ := V \ (↑t : Set ℂ)
  have hU_open : IsOpen U := by
    -- The thickened collar is open, and removing a finite set preserves openness.
    simpa [U, V] using IsOpen.sdiff Metric.isOpen_thickening t.finite_toSet.isClosed
  have hU_sub_L : U ⊆ L' := by
    intro z hz
    exact hVL hz.1
  refine ⟨U, hU_open, ?_, ?_, ?_⟩
  · -- Points of `K` survive the finite deletion because collar support points of `K` already lie
    -- in the original support finset.
    intro z hzK
    refine ⟨hKV hzK, ?_⟩
    intro hzT
    have hz_not_s : z ∉ s := (Finset.mem_sdiff.mp hzT).2
    have hz_not_supportK : z ∉ (MeromorphicOn.divisor g K).support := by
      intro hz_supportK
      exact hz_not_s ((Set.Finite.mem_toFinset hsupportK).2 hz_supportK)
    have hdivK : MeromorphicOn.divisor g K z = 0 := by
      rw [Function.mem_support] at hz_not_supportK
      exact not_ne_iff.mp hz_not_supportK
    have hrestrictLK :=
      congrArg (fun F : Function.locallyFinsuppWithin K ℤ ↦ F z)
        (MeromorphicOn.divisor_restrict (U := L') (V := K) hgL hKL)
    have hdivL : MeromorphicOn.divisor g L' z = 0 := by
      have hdivLK :
          MeromorphicOn.divisor g L' z = MeromorphicOn.divisor g K z := by
        simpa [Function.locallyFinsuppWithin.restrict_apply, hzK] using hrestrictLK
      rw [hdivLK, hdivK]
    have hz_supportL : z ∈ (MeromorphicOn.divisor g L').support := by
      exact (Set.Finite.mem_toFinset hsupportL).1 ((Finset.mem_sdiff.mp hzT).1)
    rw [Function.mem_support] at hz_supportL
    exact hz_supportL hdivL
  · -- The owner `U` stays inside the original open domain because the whole collar does.
    intro z hzU
    exact hLD (hU_sub_L hzU)
  · -- Outside the original support finset `s`, the deleted collar removes all remaining divisor
    -- support points.
    intro z hzU hz_not_s
    have hz_not_t : z ∉ t := hzU.2
    have hz_not_supportL : z ∉ (MeromorphicOn.divisor g L').support := by
      intro hz_supportL
      have hz_supportL_fin : z ∈ hsupportL.toFinset :=
        (Set.Finite.mem_toFinset hsupportL).2 hz_supportL
      exact hz_not_t (Finset.mem_sdiff.mpr ⟨hz_supportL_fin, hz_not_s⟩)
    have hdivL : MeromorphicOn.divisor g L' z = 0 := by
      rw [Function.mem_support] at hz_not_supportL
      exact not_ne_iff.mp hz_not_supportL
    have hrestrictLU :=
      congrArg (fun F : Function.locallyFinsuppWithin U ℤ ↦ F z)
        (MeromorphicOn.divisor_restrict (U := L') (V := U) hgL hU_sub_L)
    simpa [Function.locallyFinsuppWithin.restrict_apply, hzU, hdivL] using hrestrictLU.symm

/-- Helper for Proposition 5.2: after replacing `g` by `toMeromorphicNFOn g U`, the divisor read
on the open owner `U` agrees with the original divisor read on the compact owner `K`. -/
lemma divisor_toMeromorphicNFOn_eq_divisor_on_compact_owner
    {D K U : Set ℂ} {g : ℂ → ℂ} (hg : MeromorphicOn g D)
    (hKU : K ⊆ U) (hUD : U ⊆ D) {z : ℂ} (hz : z ∈ K) :
    MeromorphicOn.divisor (toMeromorphicNFOn g U) U z =
      MeromorphicOn.divisor g K z := by
  have hgU : MeromorphicOn g U := hg.mono_set hUD
  have hrestrict :=
    congrArg (fun F : Function.locallyFinsuppWithin K ℤ ↦ F z)
      (MeromorphicOn.divisor_restrict (U := U) (V := K) hgU hKU)
  -- First remove the normal-form replacement on `U`, then restrict the divisor from `U` to `K`.
  calc
    MeromorphicOn.divisor (toMeromorphicNFOn g U) U z
        = MeromorphicOn.divisor g U z := by
            simpa using congrArg (fun F : Function.locallyFinsuppWithin U ℤ ↦ F z)
              hgU.divisor_of_toMeromorphicNFOn
    _ = MeromorphicOn.divisor g K z := by
      simpa [Function.locallyFinsuppWithin.restrict_apply, hz] using hrestrict

/-- Helper for Proposition 5.2: at a nonzero compact-owner divisor support point, the
normal-form owner has exactly the corresponding finite meromorphic order. -/
lemma meromorphicOrderAt_toMeromorphicNFOn_eq_of_divisor_ne_zero
    {D K U : Set ℂ} {g : ℂ → ℂ} {z : ℂ} (hg : MeromorphicOn g D)
    (hKU : K ⊆ U) (hUD : U ⊆ D) (hzK : z ∈ K) (hzU : z ∈ U)
    (hdiv_ne : MeromorphicOn.divisor g K z ≠ 0) :
    meromorphicOrderAt (toMeromorphicNFOn g U) z =
      (MeromorphicOn.divisor g K z : WithTop ℤ) := by
  let gNF : ℂ → ℂ := toMeromorphicNFOn g U
  have hgNF : MeromorphicNFOn gNF U := by
    simpa [gNF] using meromorphicNFOn_toMeromorphicNFOn g U
  have hdivisor :
      MeromorphicOn.divisor gNF U z = MeromorphicOn.divisor g K z := by
    -- First read the normal-form divisor on `U`, then restrict it back to the compact owner `K`.
    simpa [gNF] using
      divisor_toMeromorphicNFOn_eq_divisor_on_compact_owner
        (D := D) (K := K) (U := U) (g := g) hg hKU hUD hzK
  have horder_untop :
      (meromorphicOrderAt gNF z).untop₀ = MeromorphicOn.divisor g K z := by
    calc
      (meromorphicOrderAt gNF z).untop₀ = MeromorphicOn.divisor gNF U z := by
        rw [hgNF.meromorphicOn.divisor_apply hzU]
      _ = MeromorphicOn.divisor g K z := hdivisor
  have hnot_top : meromorphicOrderAt gNF z ≠ ⊤ := by
    intro htop
    have hzero : MeromorphicOn.divisor g K z = 0 := by
      rw [← horder_untop, htop]
      simp
    exact hdiv_ne hzero
  calc
    meromorphicOrderAt gNF z = ↑((meromorphicOrderAt gNF z).untop₀) := by
      symm
      exact WithTop.coe_untop₀_of_ne_top hnot_top
    _ = (MeromorphicOn.divisor g K z : WithTop ℤ) := by
      exact congrArg (fun n : ℤ ↦ (n : WithTop ℤ)) horder_untop

/-- Helper for Proposition 5.2: codiscrete equality on an open owner `U` transfers to equality of
each boundary-component integral whose path image lies inside `U`. -/
lemma curveIntegral_eq_of_codiscrete_boundary_component
    {ι : Type u} [Fintype ι] {K U : Set ℂ} (Γ : ι → ClosedPath ℂ)
    (hΓ : IsOrientedBoundaryOf K Γ) (i : ι) {φ ψ : ℂ → ℂ}
    (hEq : φ =ᶠ[Filter.codiscreteWithin U] ψ)
    (hRange : Set.range ((Γ i).toPath) ⊆ U) :
    ∫ᶜ z in (Γ i).toPath, ((φ dz) z) = ∫ᶜ z in (Γ i).toPath, ((ψ dz) z) := by
  let γ := (Γ i).toPath
  let A : Set ℂ := {z | φ z = ψ z}
  have hA_U : A ∈ Filter.codiscreteWithin U := by
    simpa [A, Filter.EventuallyEq] using hEq
  have hA_range : A ∈ Filter.codiscreteWithin (Set.range γ) := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hA_U ⊢
    intro z hzRange
    have hzU : z ∈ U := hRange (by simpa [γ] using hzRange)
    -- Restrict the codiscrete equality from the ambient owner `U` to the compact path image.
    refine Filter.mem_of_superset (hA_U z hzU) ?_
    intro w hw
    rcases hw with hwA | hwUc
    · exact Or.inl hwA
    · exact Or.inr fun hwRange ↦ hwUc (hRange (by simpa [γ] using hwRange))
  have hBadImage : (Set.range γ \ A).Finite := by
    -- Compactness of the path image turns codiscrete equality into finiteness of the bad image.
    exact (isCompact_range γ.continuous).finite_diff_of_mem_codiscreteWithin hA_range
  let B : Set ℝ := (γ.extend ⁻¹' (Set.range γ \ A)) ∩ Set.uIoc (0 : ℝ) 1
  have hBadParam : B.Finite := by
    -- On `Set.uIoc (0,1]`, the boundary-component parametrization is injective.
    simpa [B, γ] using
      boundary_component_finite_preimage_uIoc
        (K := K) (Γ := Γ) hΓ i hBadImage
  have hParamEq :
      (fun t : ℝ ↦ (((φ dz) (γ.extend t)) (deriv γ.extend t)))
        =ᶠ[Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)]
      (fun t : ℝ ↦ (((ψ dz) (γ.extend t)) (deriv γ.extend t))) := by
    change
      {t : ℝ |
          (((φ dz) (γ.extend t)) (deriv γ.extend t)) =
            (((ψ dz) (γ.extend t)) (deriv γ.extend t))} ∈
        Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1)
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    have hBadParam_cod :
        ({t : ℝ | t ∉ B} : Set ℝ) ∈
          Filter.codiscreteWithin (Set.uIoc (0 : ℝ) 1) :=
      compl_finite_mem_codiscreteWithin (s := Set.uIoc (0 : ℝ) 1) hBadParam
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hBadParam_cod
    intro t ht
    -- Outside the finite bad parameter set, the path value avoids the finite bad image.
    refine Filter.mem_of_superset (hBadParam_cod t ht) ?_
    intro u hu
    rcases hu with huNotB | huOutside
    · by_cases huI : u ∈ Set.uIoc (0 : ℝ) 1
      · have huNotPre : u ∉ γ.extend ⁻¹' (Set.range γ \ A) := by
          intro huPre
          exact huNotB ⟨huPre, huI⟩
        have huIoc : u ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa using huI
        have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt huIoc.1, huIoc.2⟩
        have huRange : γ.extend u ∈ Set.range γ := by
          refine ⟨⟨u, huIcc⟩, ?_⟩
          simpa [γ, Path.extend_apply (γ := γ) huIcc]
        have huA : γ.extend u ∈ A := by
          by_contra huA
          exact huNotPre ⟨huRange, huA⟩
        have huEq : φ (γ.extend u) = ψ (γ.extend u) := by
          simpa [A] using huA
        have huParam :
            u ∈
              {t : ℝ |
                (((φ dz) (γ.extend t)) (deriv γ.extend t)) =
                  (((ψ dz) (γ.extend t)) (deriv γ.extend t))} := by
          simp [huEq]
        exact Or.inl huParam
      · exact Or.inr huI
    · exact Or.inr huOutside
  -- Once the parameter integrands agree codiscretely on `Set.uIoc (0,1]`, the two curve
  -- integrals are equal.
  simpa [γ] using curveIntegral_eq_of_codiscrete_param_integrand
    γ hParamEq
