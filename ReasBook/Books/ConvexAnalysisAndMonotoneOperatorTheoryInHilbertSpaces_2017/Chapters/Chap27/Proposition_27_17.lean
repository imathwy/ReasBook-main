import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Definition_6_22
import BauschkeLean.Chap06.Example_6_40
import BauschkeLean.Chap15.Definition_15_24_1
import BauschkeLean.Chap16.Example_16_13
import BauschkeLean.Chap16.Theorem_16_58
import BauschkeLean.Chap17.Proposition_17_48
import BauschkeLean.Chap27.Theorem_27_2

open Set
open ContinuousLinearMap
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section ConeConstraints

variable {H : Type u} {G : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

-- Semantic recall: `lean_leansearch` only surfaced generic cone APIs here; the verified
-- project-facing owners for this item are `effectiveDomain`, `compositePrimalObjective`,
-- `Kᵒ⊖`, `Set.IsPolyhedral`, and the Chapter 27 composite-optimality surface.

/-- Source-faithful packaging of the three regularity alternatives in Proposition 27.17 for the
cone-constrained composite objective `x ↦ f x + ι[K] (L x)`. -/
inductive ConeConstraintRegularity
    (f : H → Set.Ioi (⊥ : EReal)) (K : Set G) (L : H →L[ℝ] G) : Prop where
  | closed_subspace
      (V : Submodule ℝ G)
      (hEq : K - cone (L '' effectiveDomain f) = (V : Set G))
      (hClosed : IsClosed (V : Set G)) :
      ConeConstraintRegularity f K L
  | finite_dimensional_polyhedral_ri
      (hfin : FiniteDimensional ℝ G)
      (hpolyK : K.IsPolyhedral)
      (hri : (K ∩ relativeInterior (L '' effectiveDomain f)).Nonempty) :
      ConeConstraintRegularity f K L
  | finite_dimensional_polyhedral_function
      (hfinH : FiniteDimensional ℝ H)
      (hfinG : FiniteDimensional ℝ G)
      (hpolyf : Polyhedral f.asEReal)
      (hpolyK : K.IsPolyhedral)
      (hfeas : (K ∩ L '' effectiveDomain f).Nonempty) :
      ConeConstraintRegularity f K L

variable {f : H → Set.Ioi (⊥ : EReal)} {K : Set G} {L : H →L[ℝ] G} {xbar : H}

/-- Helper for Proposition 27.17: the product of a polyhedral set with the nonnegative half-line
is polyhedral. -/
private theorem Set.IsPolyhedral.prodIciZero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : C.IsPolyhedral) :
    (C ×ˢ Set.Ici (0 : ℝ)).IsPolyhedral := by
  classical
  rcases hC with ⟨t, hCeq⟩
  refine ⟨
    t.image (fun p : (E →L[ℝ] ℝ) × ℝ ↦ (p.1.comp (ContinuousLinearMap.fst ℝ E ℝ), p.2)) ∪
      {(-ContinuousLinearMap.snd ℝ E ℝ, (0 : ℝ))},
    ?_⟩
  ext q
  rcases q with ⟨x, r⟩
  rw [hCeq]
  simp only [mem_prod, mem_iInter, Prod.forall, mem_Ici, Finset.union_singleton,
    Finset.mem_insert, Finset.mem_image, Prod.exists, iInter_iInter_eq_or_left,
    iInter_exists, mem_inter_iff, and_imp, Prod.mk.injEq]
  constructor
  · rintro ⟨hxt, hr⟩
    refine ⟨?_, ?_⟩
    · simpa [Set.mem_closedHalfspace_iff] using hr
    intro a b i i₁ hi hcomp hb
    subst hcomp hb
    exact hxt i i₁ hi
  · rintro ⟨hr, hprod⟩
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hprod _ _ a b hab rfl rfl
    · simpa [Set.mem_closedHalfspace_iff] using hr

omit [CompleteSpace G] in
/-- Helper for Proposition 27.17: the indicator of a polyhedral cone is a polyhedral
extended-real-valued function. -/
private theorem indicatorAsEReal_polyhedral_of_isPolyhedral
    (hK_polyhedral : K.IsPolyhedral) :
    Polyhedral (ι[K]).asEReal := by
  -- Rewrite the epigraph as `K × ℝ≥0` and reuse the polyhedral-product description.
  rw [polyhedral_iff]
  have hprod : (K ×ˢ Set.Ici (0 : ℝ)).IsPolyhedral :=
    Set.IsPolyhedral.prodIciZero hK_polyhedral
  have hepigraph :
      epigraph (ι[K]).asEReal = K ×ˢ Set.Ici (0 : ℝ) := by
    ext p
    rcases p with ⟨x, t⟩
    rw [mem_epigraph_iff]
    by_cases hx : x ∈ K
    · simp [ERealFunction.indicator, hx]
    · simp [ERealFunction.indicator, hx]
  simpa [hepigraph]

/-- The three source regularity alternatives in Proposition 27.17 specialize the Chapter 27
composite-regularity owner for `g = ι[K]`. -/
theorem ConeConstraintRegularity.toCompositePrimalObjectiveRegularity
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (_hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hqual : ConeConstraintRegularity f K L) :
    CompositePrimalObjectiveRegularity f (ι[K]) L := by
  -- Route correction: map each source regularity branch directly to the matching Chapter 27
  -- composite regularity owner for `g = ι[K]`.
  cases hqual with
  | closed_subspace V hEq hClosed =>
      have howner :
          strongRelativeInteriorSubImageRegularity (effectiveDomain f) K L := by
        -- The cone branch of Proposition 6.19 matches the source clause `K - cone (L (dom f))`.
        refine Or.inr <| Or.inr <| Or.inl ?_
        refine ⟨hK_cone, ?_, ?_⟩
        · rw [hEq, Submodule.span_eq]
        · simpa [hEq, Submodule.span_eq] using hClosed
      have hsri :
          (0 : G) ∈ sri (K - L '' effectiveDomain f) := by
        -- Proposition 6.19 supplies the origin-in-`sri` consequence for the source predicate.
        exact
          zero_mem_strongRelativeInterior_sub_image_of_regularity
            hf.2.nonempty
            hK_nonempty
            hf.2.convex_effectiveDomain
            hK_convex
            L howner
      have hsri' :
          (0 : G) ∈ sri (effectiveDomain (ι[K]) - L '' effectiveDomain f) := by
        simpa using hsri
      exact CompositePrimalObjectiveRegularity.zero_mem_sri hsri'
  | finite_dimensional_polyhedral_ri hfin hpolyK hri =>
      -- The polyhedral-indicator branch is exactly the Chapter 27
      -- `polyhedral_finiteDimensional_ri` constructor.
      refine CompositePrimalObjectiveRegularity.polyhedral_finiteDimensional_ri hfin ?_ ?_
      · simpa using indicatorAsEReal_polyhedral_of_isPolyhedral hpolyK
      · simpa using hri
  | finite_dimensional_polyhedral_function hfinH hfinG hpolyf hpolyK hfeas =>
      -- The finite-dimensional polyhedral branch maps verbatim after rewriting
      -- the indicator domain.
      refine CompositePrimalObjectiveRegularity.polyhedral_finiteDimensional
        hfinH hfinG hpolyf ?_ ?_
      · simpa using indicatorAsEReal_polyhedral_of_isPolyhedral hpolyK
      · simpa using hfeas

/-- Auxiliary witness for the polar-cone multiplier condition in Proposition 27.17 (1). -/
class PolarSubgradientWitness
    (f : H → Set.Ioi (⊥ : EReal)) (K : Set G) (L : H →L[ℝ] G)
    (xbar : H) (vbar : G) : Prop where
  mem_polarCone : vbar ∈ Kᵒ⊖
  mem_subdifferential : -L.adjoint vbar ∈ (∂ f) xbar
  complementary_slackness : ⟪L xbar, vbar⟫_ℝ = 0

/-- The source-facing complementarity equation can be rewritten in the affine-tilt form. -/
theorem PolarSubgradientWitness.complementary_slackness_adjoint
    {vbar : G} (hvbar : PolarSubgradientWitness f K L xbar vbar) :
    ⟪xbar, L.adjoint vbar⟫_ℝ = 0 := by
  -- Rewrite the pairing through the adjoint and reuse the stored complementarity equation.
  calc
    ⟪xbar, L.adjoint vbar⟫_ℝ = ⟪L xbar, vbar⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = 0 := hvbar.complementary_slackness

/-- Auxiliary witness for the gradient specialization in Proposition 27.17 (3). -/
class PolarGradientWitness
    (K : Set G) (L : H →L[ℝ] G) (xbar gradf : H) (vbar : G) : Prop where
  mem_polarCone : vbar ∈ Kᵒ⊖
  gradient_eq_neg_adjoint : gradf = -L.adjoint vbar
  complementary_slackness : ⟪L xbar, vbar⟫_ℝ = 0

/-- The gradient witness also admits the affine-tilt complementarity form. -/
theorem PolarGradientWitness.complementary_slackness_adjoint
    {gradf : H} {vbar : G} (hvbar : PolarGradientWitness K L xbar gradf vbar) :
    ⟪xbar, L.adjoint vbar⟫_ℝ = 0 := by
  -- The adjoint rewrite is identical to the subgradient-witness case.
  calc
    ⟪xbar, L.adjoint vbar⟫_ℝ = ⟪L xbar, vbar⟫_ℝ := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    _ = 0 := hvbar.complementary_slackness

/-- The first clause of Proposition 27.17: under any of the three source regularity hypotheses,
`xbar` solves the
cone-constrained problem `minimize f x` subject to `L x ∈ K` if and only if `L xbar ∈ K` and
there exists a polar-cone multiplier `vbar ∈ Kᵒ⊖` with `-L^* vbar ∈ ∂ f xbar` and
`⟪L xbar, vbar⟫ = 0`, packaged as `PolarSubgradientWitness`. -/
theorem mem_argmin_coneConstraintObjective_iff_exists_polar_subgradient
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hqual : ConeConstraintRegularity f K L) :
    xbar ∈ Argmin (compositePrimalObjective f (ι[K]) L) ↔
      L xbar ∈ K ∧
        ∃ vbar : G, PolarSubgradientWitness f K L xbar vbar := by
  have hIndicator : (ι[K] : G → Set.Ioi (⊥ : EReal)) ∈ Γ₀(G) :=
    indicator_mem_gammaZero_of_nonempty_isClosed_convex hK_nonempty hK_closed hK_convex
  have hregular :
      CompositePrimalObjectiveRegularity f (ι[K]) L :=
    hqual.toCompositePrimalObjectiveRegularity hf hK_nonempty hK_closed hK_convex hK_cone
  have howner :
      xbar ∈ Argmin (compositePrimalObjective f (ι[K]) L) ↔
        xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L (ι[K])).zeros :=
    mem_argmin_compositePrimalObjective_iff_mem_zeros_subdifferential_sum_of_regular
      hf hIndicator L hregular
  constructor
  · intro hx
    have hzero :
        xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L (ι[K])).zeros :=
      howner.mp hx
    rcases
        (mem_zeros_subdifferential_sum_iff_exists_mem_subdifferential L).1 hzero with
      ⟨vbar, hvbar, hsub⟩
    have hnormal : vbar ∈ N[K] (L xbar) := by
      rw [← subdifferential_setIndicator_eq_normalCone K hK_nonempty]
      exact hvbar
    have hfeas : L xbar ∈ K := by
      by_contra hxK
      have : vbar ∈ (∅ : Set G) := by
        rw [Set.normalCone_of_not_mem hxK] at hnormal
        exact hnormal
      simp at this
    have hpolar :
        vbar ∈ Kᵒ⊖ ∩ Set.orthogonalSet ({L xbar} : Set G) := by
      rw [normalCone_eq_polarCone_inter_orthogonalSet_singleton_of_mem_convex_cone
        hK_cone hK_convex hfeas] at hnormal
      rcases hnormal with ⟨hneg, horth⟩
      refine ⟨?_, horth⟩
      rw [Set.mem_polarCone_iff_forall_inner_nonpos]
      exact (Set.mem_negativePolar.mp hneg)
    rcases hpolar with ⟨hpolarCone, horth⟩
    have hslack : ⟪L xbar, vbar⟫_ℝ = 0 := by
      rw [Set.mem_orthogonalSet] at horth
      exact horth (L xbar) (by simp)
    refine ⟨hfeas, vbar, ?_⟩
    exact ⟨hpolarCone, hsub, hslack⟩
  · rintro ⟨hfeas, vbar, hvbar⟩
    have hnegative : vbar ∈ Set.negativePolar K := by
      rw [Set.mem_negativePolar]
      exact (Set.mem_polarCone_iff_forall_inner_nonpos.mp hvbar.mem_polarCone)
    have hnormal : vbar ∈ N[K] (L xbar) := by
      rw [normalCone_eq_polarCone_inter_orthogonalSet_singleton_of_mem_convex_cone
        hK_cone hK_convex hfeas]
      refine ⟨hnegative, ?_⟩
      rw [Set.mem_orthogonalSet]
      intro y hy
      have hyx : y = L xbar := by simpa using hy
      simpa [hyx] using hvbar.complementary_slackness
    have hvIndicator : vbar ∈ (∂ ι[K]) (L xbar) := by
      rw [subdifferential_setIndicator_eq_normalCone K hK_nonempty]
      exact hnormal
    have hzero :
        xbar ∈ ((∂ f) + ContinuousLinearMap.adjointImageSubdifferential L (ι[K])).zeros := by
      exact
        (mem_zeros_subdifferential_sum_iff_exists_mem_subdifferential L).2
          ⟨vbar, hvIndicator, hvbar.mem_subdifferential⟩
    exact howner.mpr hzero

/-- The affine-tilt consequence of Proposition 27.17: in the optimality system above, the
multiplier `vbar` yields the
affine-tilted unconstrained minimization problem
`minimize affineTiltEReal f.asEReal (-L^* vbar)`. -/
theorem mem_argmin_affineTilt_of_polar_subgradient
    {vbar : G}
    (hfeas : L xbar ∈ K)
    (hvbar : PolarSubgradientWitness f K L xbar vbar) :
    xbar ∈ Argmin (affineTiltEReal f.asEReal (-L.adjoint vbar)) := by
  have hsource : L xbar ∈ K ∧ ⟪xbar, L.adjoint vbar⟫_ℝ = 0 := by
    -- Keep the feasibility/complementarity package explicit because it is the source-facing data.
    exact ⟨hfeas, hvbar.complementary_slackness_adjoint⟩
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro y
  let a : H := L.adjoint vbar
  have hsub :
      (⟪y - xbar, -a⟫_ℝ : EReal) + (f xbar : EReal) ≤ (f y : EReal) :=
    (mem_subdifferential_iff f xbar (-a)).1
      hvbar.mem_subdifferential y
  have hsubPair : ⟪y - xbar, a⟫_ℝ = ⟪y, a⟫_ℝ := by
    -- Complementarity removes the `xbar` contribution from the translated inner product.
    calc
      ⟪y - xbar, a⟫_ℝ = ⟪y, a⟫_ℝ - ⟪xbar, a⟫_ℝ := by
        rw [inner_sub_left]
      _ = ⟪y, a⟫_ℝ := by
        rw [hsource.2]
        ring
  have hrew :
      (-((⟪y, a⟫_ℝ : ℝ) : EReal)) + (f xbar : EReal) ≤ (f y : EReal) := by
    have hsub' := hsub
    rw [inner_neg_right, hsubPair] at hsub'
    simpa using hsub'
  have hadded :
      (f xbar : EReal) ≤ (f y : EReal) + (⟪y, a⟫_ℝ : EReal) := by
    have hshift := add_le_add_right hrew (⟪y, a⟫_ℝ : EReal)
    have hcancel :
        (⟪y, a⟫_ℝ : EReal) + (-((⟪y, a⟫_ℝ : ℝ) : EReal) + (f xbar : EReal)) =
          (f xbar : EReal) := by
      calc
        (⟪y, a⟫_ℝ : EReal) + (-((⟪y, a⟫_ℝ : ℝ) : EReal) + (f xbar : EReal))
            = ((⟪y, a⟫_ℝ : EReal) + -((⟪y, a⟫_ℝ : ℝ) : EReal)) + (f xbar : EReal) := by
                simp [add_assoc]
        _ = ((((⟪y, a⟫_ℝ : ℝ) : EReal) + (((-⟪y, a⟫_ℝ : ℝ) : EReal))) + (f xbar : EReal)) := by
              rw [← EReal.coe_neg]
        _ = (((⟪y, a⟫_ℝ + -⟪y, a⟫_ℝ : ℝ) : EReal)) + (f xbar : EReal) := by
              rw [← EReal.coe_add]
        _ = (0 : EReal) + (f xbar : EReal) := by
              congr 1
              ring_nf
              simp
        _ = (f xbar : EReal) := by
              simp
    rw [hcancel] at hshift
    simpa [add_comm] using hshift
  calc
    affineTiltEReal f.asEReal (-L.adjoint vbar) xbar = (f xbar : EReal) := by
      simp [affineTiltEReal, hsource.2]
    _ ≤ (f y : EReal) + (⟪y, a⟫_ℝ : EReal) := hadded
    _ = affineTiltEReal f.asEReal (-L.adjoint vbar) y := by
      simp [affineTiltEReal, a]

omit [CompleteSpace H] in
/-- Helper for Proposition 27.17: a finite source directional derivative keeps the positive ray
inside `effectiveDomain f` near the base point. -/
private theorem eventually_mem_effectiveDomain_of_hasDirectionalDerivativeAt_real
    {x d : H} {ξ : ℝ}
    (hξ : HasDirectionalDerivativeAt f x d (ξ : EReal)) :
    ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f := by
  let q : ℝ → EReal := fun α ↦ ((f (x + α • d) : EReal) - (f x : EReal)) / α
  have hfinite :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), q α ∈ Set.Ioo (⊥ : EReal) ⊤ := by
    -- Near the finite derivative value `ξ`, the quotient must stay finite.
    exact hξ.2 (isOpen_Ioo.mem_nhds (by simp))
  -- If a nearby ray point left the effective domain, the quotient would jump to `⊤`.
  filter_upwards [hfinite, self_mem_nhdsWithin] with α hαfinite hα
  rw [mem_effectiveDomain_iff]
  by_contra hαdom
  have hαtop : (f (x + α • d) : EReal) = ⊤ := by
    exact le_antisymm le_top (not_lt.mp hαdom)
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hξ.1)
  have hqtop : q α = ⊤ := by
    dsimp [q]
    rw [hαtop, EReal.top_sub hx_top, EReal.top_div_of_pos_ne_top]
    · exact_mod_cast hα
    · exact EReal.coe_ne_top α
  exact hαfinite.2.ne hqtop

omit [CompleteSpace H] in
/-- Helper for Proposition 27.17: along finite ray points, the source extended-real quotient is
the coercion of the ordinary real quotient for `toReal`. -/
private theorem differenceQuotientEqCoeToRealOfMemEffectiveDomain
    {x d : H} (hx : x ∈ effectiveDomain f) {α : ℝ} (hα : 0 < α)
    (hαdom : x + α • d ∈ effectiveDomain f) :
    (((f (x + α • d) : EReal) - (f x : EReal)) / α) =
      ((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal) := by
  -- Rewrite both finite endpoint values through `toReal`, then the quotient is purely real.
  have _ : α ≠ 0 := hα.ne'
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hαdom_top : (f (x + α • d) : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hαdom)
  have hαdom_bot : (f (x + α • d) : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f (x + α • d) : EReal) from (f (x + α • d)).2)
  rw [← EReal.coe_toReal hαdom_top hαdom_bot, ← EReal.coe_toReal hx_top hx_bot,
    ← EReal.coe_sub, ← EReal.coe_div]
  simp

omit [CompleteSpace H] in
/-- Helper for Proposition 27.17: the source Gâteaux data and the real-valued Gâteaux gradient
produce the directional-derivative family needed to identify `(∂ f) xbar` with `{gradf}`. -/
private theorem hasDirectionalDerivativeAt_toDualMap_of_eventually_mem_effectiveDomain
    {gradf : H} {x d : H}
    (hx : x ∈ effectiveDomain f)
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f y : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H gradf) x)
    (hevent : ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + α • d ∈ effectiveDomain f) :
    HasDirectionalDerivativeAt f x d
      ((((InnerProductSpace.toDualMap ℝ H gradf) d : ℝ) : EReal)) := by
  have hreal :
      Filter.Tendsto
        (fun α : ℝ ↦ (((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((InnerProductSpace.toDualMap ℝ H gradf) d)) := by
    -- The Gâteaux derivative gives the real-valued quotient limit along the ray.
    simpa [one_div, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hgrad.tendsto_directionalDifferenceQuotient d
  have hcoe :
      Filter.Tendsto
        (fun α : ℝ ↦
          (((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((((InnerProductSpace.toDualMap ℝ H gradf) d : ℝ) : EReal))) :=
    EReal.tendsto_coe.2 hreal
  have hEq :
      (fun α : ℝ ↦ ((f (x + α • d) : EReal) - (f x : EReal)) / α) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun α : ℝ ↦
          (((((f (x + α • d) : EReal).toReal - (f x : EReal).toReal) / α : ℝ) : EReal))) := by
    -- Along the effective-domain branch, the source quotient is exactly the cast real quotient.
    filter_upwards [hevent, self_mem_nhdsWithin] with α hαdom hα
    simpa using
      differenceQuotientEqCoeToRealOfMemEffectiveDomain (f := f) hx hα hαdom
  exact ⟨hx, Filter.Tendsto.congr' hEq.symm hcoe⟩

omit [CompleteSpace H] in
/-- Helper for Proposition 27.17: the source Gâteaux data and the real-valued Gâteaux gradient
produce the directional-derivative family needed to identify `(∂ f) xbar` with `{gradf}`. -/
private theorem hasDirectionalDerivativeAt_toDualMap_of_gateauxData
    {gradf : H}
    (hx : xbar ∈ effectiveDomain f)
    (hgateaux : ERealFunction.GateauxDifferentiableAt f xbar)
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f y : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H gradf) xbar) :
    ∀ y : H,
      HasDirectionalDerivativeAt f xbar y
        ((((InnerProductSpace.toDualMap ℝ H gradf) y : ℝ) : EReal)) := by
  rcases hgateaux with ⟨A, hA⟩
  intro y
  have hevent :
      ∀ᶠ α in nhdsWithin (0 : ℝ) (Set.Ioi 0), xbar + α • y ∈ effectiveDomain f :=
    eventually_mem_effectiveDomain_of_hasDirectionalDerivativeAt_real (f := f) (hA y)
  -- The local quotient bridge upgrades the real-valued derivative to the source directional
  -- derivative once the ray is known to stay in the effective domain.
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    hasDirectionalDerivativeAt_toDualMap_of_eventually_mem_effectiveDomain
      (f := f) (x := xbar) (d := y) hx hgrad hevent

/-- Helper for Proposition 27.17: a singleton subdifferential turns a polar-subgradient witness
into the gradient witness from clause `(3)`. -/
private theorem polarGradientWitnessOfPolarSubgradientWitness
    {gradf : H} {vbar : G}
    (hsingle : (∂ f) xbar = ({gradf} : Set H))
    (hvbar : PolarSubgradientWitness f K L xbar vbar) :
    PolarGradientWitness K L xbar gradf vbar := by
  have hgrad_eq : gradf = -L.adjoint vbar := by
    -- The singleton subdifferential identifies the KKT subgradient with `gradf`.
    have hgrad_eq' : -L.adjoint vbar = gradf := by
      simpa [hsingle] using hvbar.mem_subdifferential
    exact hgrad_eq'.symm
  exact ⟨hvbar.mem_polarCone, hgrad_eq, hvbar.complementary_slackness⟩

/-- Helper for Proposition 27.17: a gradient witness becomes a polar-subgradient witness once
`(∂ f) xbar` is known to equal `{gradf}`. -/
private theorem polarSubgradientWitnessOfPolarGradientWitness
    {gradf : H} {vbar : G}
    (hsingle : (∂ f) xbar = ({gradf} : Set H))
    (hvbar : PolarGradientWitness K L xbar gradf vbar) :
    PolarSubgradientWitness f K L xbar vbar := by
  have hgrad_mem : gradf ∈ (∂ f) xbar := by
    -- The singleton equality exhibits `gradf` as the unique subgradient at `xbar`.
    simp [hsingle]
  have hsub : -L.adjoint vbar ∈ (∂ f) xbar := by
    -- Rewrite the unique subgradient through the gradient witness identity.
    simpa [hvbar.gradient_eq_neg_adjoint] using hgrad_mem
  exact ⟨hvbar.mem_polarCone, hsub, hvbar.complementary_slackness⟩

/-- Proposition 27.17 (3): if `f` is Gâteaux differentiable at the effective-domain point `xbar`
in the Chapter 17 sense and `gradf` is a representing Gâteaux gradient of its finite real
representative there, then the
subgradient condition in clause `(1)` is equivalently the concrete identity
`gradf = -L^* vbar`. -/
theorem mem_argmin_coneConstraintObjective_iff_exists_polar_gradient
    (hf : f ∈ Γ₀(H))
    (hK_nonempty : K.Nonempty) (hK_closed : IsClosed K)
    (hK_convex : Convex ℝ K) (hK_cone : IsCone K)
    (hqual : ConeConstraintRegularity f K L)
    {gradf : H}
    (hxbar : xbar ∈ effectiveDomain f)
    (hgateaux : ERealFunction.GateauxDifferentiableAt f xbar)
    (hgrad :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f y : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H gradf) xbar) :
    xbar ∈ Argmin (compositePrimalObjective f (ι[K]) L) ↔
      L xbar ∈ K ∧
        ∃ vbar : G, PolarGradientWitness K L xbar gradf vbar := by
  -- Route correction: avoid Proposition 17.31's placeholder singleton-subdifferential API.
  -- Instead, reuse clause `(1)`, build the directional-derivative family from Chapter 17.21,
  -- collapse `(∂ f) xbar` to `{gradf}`, and then convert the witness records.
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  have hkkt :
      xbar ∈ Argmin (compositePrimalObjective f (ι[K]) L) ↔
        L xbar ∈ K ∧ ∃ vbar : G, PolarSubgradientWitness f K L xbar vbar :=
    mem_argmin_coneConstraintObjective_iff_exists_polar_subgradient
      (hf := hf) hK_nonempty hK_closed hK_convex hK_cone hqual
  have hdir :
      ∀ y : H,
        HasDirectionalDerivativeAt f xbar y
          ((((InnerProductSpace.toDualMap ℝ H gradf) y : ℝ) : EReal)) :=
    hasDirectionalDerivativeAt_toDualMap_of_gateauxData
      (f := f) (xbar := xbar) (gradf := gradf) hxbar hgateaux hgrad
  have hsingle :
      (∂ f) xbar = ({gradf} : Set H) :=
    subdifferential_eq_singleton_of_forall_hasDirectionalDerivativeAt
      (g := f) (hg := hf) (x := xbar) (gradg := gradf) hdir
  constructor
  · intro hx
    -- Clause `(1)` gives the cone KKT witness; the singleton subdifferential upgrades it to the
    -- explicit gradient identity from clause `(3)`.
    rcases hkkt.mp hx with ⟨hfeas, vbar, hvbar⟩
    exact ⟨hfeas, ⟨vbar,
      polarGradientWitnessOfPolarSubgradientWitness
        (f := f) (K := K) (L := L) (xbar := xbar) hsingle hvbar⟩⟩
  · rintro ⟨hfeas, vbar, hvbar⟩
    -- Conversely, the explicit gradient identity reconstructs the clause `(1)` KKT witness.
    exact hkkt.mpr ⟨hfeas, ⟨vbar,
      polarSubgradientWitnessOfPolarGradientWitness
        (f := f) (K := K) (L := L) (xbar := xbar) hsingle hvbar⟩⟩

end ConeConstraints

end ERealFunction
