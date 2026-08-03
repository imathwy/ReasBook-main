import BauschkeLean.Chap01.Text_1_0_57
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap09.Proposition_9_3
import BauschkeLean.Chap03.Definition_3_49
import BauschkeLean.Chap07.Definition_7_8
import BauschkeLean.Chap07.Exercise_7_1
import BauschkeLean.Chap11.Proposition_11_1
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap11.Example_11_2
import BauschkeLean.Chap13.Example_13_3
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap14.Proposition_14_11
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Local `ℓ²` product seminormed-group instance used by the product-graph support helper for
Example 15.29. -/
local instance prod_seminormedAddCommGroup_l2_support : SeminormedAddCommGroup (H × K) :=
  prod_seminormedAddCommGroup_l2 (H := H) (K := K)

/-- Local `ℓ²` product normed-group instance used by the product-graph support helper for Example
15.29. -/
local instance prod_normedAddCommGroup_l2_support : NormedAddCommGroup (H × K) :=
  prod_normedAddCommGroup_l2 (H := H) (K := K)

/-- Local `ℓ²` product normed-space instance used by the product-graph support helper for Example
15.29. -/
local instance prod_normedSpace_l2_support : NormedSpace ℝ (H × K) :=
  prod_normedSpace_l2 (H := H) (K := K)

/-- Local `ℓ²` product complete-space instance used by the product-graph support helper for
Example 15.29. -/
local instance prod_completeSpace_l2_support : CompleteSpace (H × K) :=
  prod_completeSpace_l2 (H := H) (K := K)

/-- Local `ℓ²` product inner-product instance used by the product-graph support helper for
Example 15.29. -/
local instance prod_innerProductSpace_l2_support : InnerProductSpace ℝ (H × K) :=
  prod_innerProductSpace_l2 (H := H) (K := K)

omit [CompleteSpace K] in
/-- Local support-function properness bridge used by the indicatorized dual helper statements in
Example 15.29. -/
private lemma supportFunction_isProper_of_nonempty_local
    (D : Set K) (hD_nonempty : D.Nonempty) :
    IsProper (σ[D]) := by
  -- This is exactly the Chapter 7 properness statement for support functions of nonempty sets.
  simpa using isProper_supportFunction_of_nonempty D hD_nonempty

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the support function is the supremum over the subtype indexing the
set. -/
private lemma supportFunction_eq_iSup_subtype_local
    (D : Set K) :
    σ[D] = fun u : K ↦ ⨆ x : D, ((⟪(x : K), u⟫_ℝ : ℝ) : EReal) := by
  funext u
  rw [supportFunction_eq_sSup_image]
  have himage :
      (fun x : K ↦ (⟪x, u⟫_ℝ : EReal)) '' D =
        Set.range (fun x : D ↦ ((⟪(x : K), u⟫_ℝ : ℝ) : EReal)) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
  rw [himage, sSup_range]

omit [CompleteSpace K] in
/-- Helper for Example 15 29: each continuous linear inner functional belongs to `Γ`. -/
private lemma inner_functional_mem_gamma_local
    (x : K) :
    (fun u : K ↦ ((⟪x, u⟫_ℝ : ℝ) : EReal)) ∈ gamma K := by
  rw [mem_gamma_iff]
  refine ⟨?_, ?_⟩
  · intro u v a ha0 ha1
    have hinner :
        ⟪x, a • u + (1 - a) • v⟫_ℝ =
          a * ⟪x, u⟫_ℝ + (1 - a) * ⟪x, v⟫_ℝ := by
      simp [inner_add_right, inner_smul_right]
    change (((⟪x, a • u + (1 - a) • v⟫_ℝ : ℝ) : EReal)) ≤
      (a : EReal) * ((⟪x, u⟫_ℝ : ℝ) : EReal) +
        (((1 - a : ℝ) : EReal) * ((⟪x, v⟫_ℝ : ℝ) : EReal))
    rw [hinner, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  · simpa using
      (continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)).lowerSemicontinuous

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the support function belongs to `Γ`. -/
private lemma supportFunction_mem_gamma_local
    (D : Set K) :
    σ[D] ∈ gamma K := by
  rw [supportFunction_eq_iSup_subtype_local]
  exact iSup_mem_gamma
    (fun x : D ↦ fun u : K ↦ ((⟪(x : K), u⟫_ℝ : ℝ) : EReal))
    (fun x ↦ inner_functional_mem_gamma_local (x : K))

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the support function is positively homogeneous. -/
private lemma supportFunction_positivelyHomogeneous_local
    (D : Set K) :
    PositivelyHomogeneous (σ[D]) := by
  intro a ha u
  simpa [Function.comp, EReal.real_smul_def] using
    congrFun (supportFunction_comp_pos_smul_eq_mul_supportFunction D ha) u

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the proper support function of a nonempty set belongs to `Γ₀`. -/
private lemma supportFunction_mem_gammaZero_local
    (D : Set K) (hD_nonempty : D.Nonempty) :
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty) ∈ Γ₀(K) := by
  exact properIoi_mem_gammaZero_of_mem_gamma
    (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    (supportFunction_mem_gamma_local D)

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the packaged support owner takes the value `0` at the origin. -/
private lemma supportOwner_zero_eq_zero_local
    (D : Set K) (hD_nonempty : D.Nonempty) :
    ((properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)) 0 : EReal) = 0 := by
  -- The support function of a nonempty set vanishes at the origin, and `properIoi` does not
  -- change finite values.
  simp [supportFunction_zero_eq_zero_of_nonempty, hD_nonempty]

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the origin lies in the effective domain of the packaged support
owner. -/
private lemma zero_mem_effectiveDomain_supportOwner_local
    (D : Set K) (hD_nonempty : D.Nonempty) :
    (0 : K) ∈ effectiveDomain
      (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)) := by
  -- The previous origin value computation witnesses finiteness at `0`.
  rw [mem_effectiveDomain_iff]
  rw [supportOwner_zero_eq_zero_local D hD_nonempty]
  simp

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the effective domain of the packaged support owner is the barrier
cone `bar D`. -/
private lemma effectiveDomain_supportOwner_eq_barrierCone_local
    (D : Set K) (hD_nonempty : D.Nonempty)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    effectiveDomain
      (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)) = bar D := by
  ext u
  -- The packaging step does not change the finite domain of the support function.
  rw [mem_effectiveDomain_iff, properIoi_apply, ← mem_dom_iff]
  simpa using
    congrArg (fun S : Set K ↦ u ∈ S)
      (show dom (σ[D]) = bar D by
        simpa [hD_closed.closure_eq, (convexHull_eq_self).2 hD_convex] using
          example_11_2_4_dom_supportFunction_eq_barrierCone (C := D))

omit [CompleteSpace K] in
/-- Helper for Example 15 29: the indicator of a nonempty closed convex set belongs to `Γ₀`. -/
private lemma indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
    (S : Set K) (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) :
    ι[S] ∈ Γ₀(K) := by
  -- Closedness gives lower semicontinuity of the indicator, and convexity controls its domain.
  have hindicator_lsc :
      LowerSemicontinuous (fun y ↦ ((ι[S]) y : EReal)) := by
    simpa using (lowerSemicontinuous_indicator_compl_top_iff_isClosed S).2 hS_closed
  have hdom : effectiveDomain (ι[S]) = S := by
    ext y
    by_cases hy : y ∈ S
    · simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
    · simp [ERealFunction.effectiveDomain, ERealFunction.indicator, hy]
  refine ⟨hindicator_lsc, ?_⟩
  refine ⟨by simpa [hdom] using hS_nonempty, fun _ hy ↦ hy, ?_⟩
  intro y hy z hz a ha0 ha1
  have hyS : y ∈ S := by
    simpa [hdom] using hy
  have hzS : z ∈ S := by
    simpa [hdom] using hz
  -- Jensen convexity for the indicator reduces to convexity of the feasible set.
  have hayzS : a • y + (1 - a) • z ∈ S :=
    hS_convex hyS hzS ha0.le (sub_nonneg.mpr ha1.le) (by ring)
  simp [ERealFunction.indicator, hyS, hzS, hayzS]

/-- Helper for Example 15 29: the indicator of a closed convex set agrees with its Fenchel
biconjugate. -/
private lemma biconjugate_indicator_eq_indicator_of_isClosed_convex_local
    (S : Set K) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) :
    ((ι[S]).asEReal)∗∗ = (ι[S]).asEReal := by
  by_cases hS_nonempty : S.Nonempty
  · have hS_gamma : ι[S] ∈ Γ₀(K) :=
      indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
        S hS_nonempty hS_closed hS_convex
    simpa using biconjugate_eq_of_mem_gammaZero hS_gamma
  · have hS_empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hS_nonempty
    have hσ_empty : σ[(∅ : Set K)] = (fun _ : K ↦ (⊥ : EReal)) := by
      ext x
      simp [innerSupremumOn_eq_sSup_image]
    ext x
    rw [conjugate_indicator_eq_supportFunction]
    simp [hS_empty, hσ_empty, ERealFunction.conjugate]

/-
Source/core/bridge triage:
- `source-facing`: Example 15.29 is the support-function saddle formula
  `inf_{x ∈ C} σ[D](Lx) = max_{v ∈ D} inf_{x ∈ C} ⟪Lx, v⟫`.
- `core/canonical`: the chapter owners are `innerInfimumOn`, `σ[C]`, and the composite Fenchel
  duality owners from Theorem 15.23.
- `bridge/view`: `innerInfimumOn_adjoint_eq_sInf_image` is the source-to-owner identification
  `inf_{x ∈ C} ⟪Lx, v⟫ = innerInfimumOn C (L.adjoint v)`, while the main theorem is the
  source-facing indicator/support-function specialization of the Chapter 15 owner theorem.
- Semantic recall note: LeanSearch did not surface the project-local support-function owners, so
  the repair keeps the verified Chapter 7/14/15 declarations already used below.
-/

-- Proof sketch: rewrite `innerInfimumOn C (L.adjoint v)` using
-- `innerInfimumOn_eq_sInf_image`, and then use the adjoint identity
-- `⟪x, L.adjoint v⟫ = ⟪L x, v⟫` to identify the image set.
/-- The dual inner infimum `innerInfimumOn C (L.adjoint v)` is exactly the infimum of the values
`⟪Lx, v⟫` over `x ∈ C`. -/
theorem innerInfimumOn_adjoint_eq_sInf_image
    (C : Set H) (L : H →L[ℝ] K) (v : K) :
    innerInfimumOn C (L.adjoint v) =
      sInf ((fun x : H ↦ (⟪L x, v⟫_ℝ : EReal)) '' C) := by
  -- Unfold the owner `innerInfimumOn`, then identify the two image sets by the adjoint formula.
  rw [innerInfimumOn_eq_sInf_image]
  congr 1
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    exact congrArg (fun r : ℝ ↦ (r : EReal))
      (ContinuousLinearMap.adjoint_inner_right L x v).symm
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    exact congrArg (fun r : ℝ ↦ (r : EReal))
      (ContinuousLinearMap.adjoint_inner_right L x v)

/-- Helper for Example 15 29: the Chapter 14 linear-minorant set of the support function of a
nonempty closed convex set recovers that set exactly. -/
private lemma linearMinorantSet_supportFunction_eq_set_local
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty) :
    linearMinorantSet
        (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)) = D := by
  let f : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  let S : Set K :=
    linearMinorantSet
      (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty))
  -- The Chapter 14 support-function representation turns the source-defined minorant set into a
  -- closed convex support owner with the same support function as `D`.
  have hph : PositivelyHomogeneous f.asEReal := by
    simpa [f] using supportFunction_positivelyHomogeneous_local D
  have hf : f ∈ Γ₀(K) := by
    simpa [f] using supportFunction_mem_gammaZero_local D hD_nonempty
  obtain ⟨hsupport, hS_nonempty, hS_closed, hS_convex⟩ :=
    eq_supportFunction_linearMinorantSet_of_positivelyHomogeneous_mem_gammaZero hph hf
  have hconj :
      ((ι[D]).asEReal)∗ = ((ι[S]).asEReal)∗ := by
    -- Both indicators have the same conjugate because both support functions are `σ[D]`.
    rw [conjugate_indicator_eq_supportFunction, conjugate_indicator_eq_supportFunction]
    simpa [S] using hsupport
  have hindicator :
      (ι[D]).asEReal = (ι[S]).asEReal := by
    -- Closed-convex indicators are equal to their biconjugates, so equal conjugates force the
    -- underlying indicators to agree.
    calc
      (ι[D]).asEReal = ((ι[D]).asEReal)∗∗ := by
        symm
        exact
          biconjugate_indicator_eq_indicator_of_isClosed_convex_local D hD_closed hD_convex
      _ = ((ι[S]).asEReal)∗∗ := by
        simpa using congrArg conjugate hconj
      _ = (ι[S]).asEReal := by
        exact
          biconjugate_indicator_eq_indicator_of_isClosed_convex_local S hS_closed hS_convex
  ext x
  by_cases hxD : x ∈ D
  · have hxS : x ∈ S := by
      by_contra hxS
      have hvalue := congrFun hindicator x
      simp [ERealFunction.indicator, hxD, hxS] at hvalue
    exact Iff.intro (fun _ ↦ hxD) (fun _ ↦ hxS)
  · have hxS : x ∉ S := by
      by_contra hxS
      have hvalue := congrFun hindicator x
      simp [ERealFunction.indicator, hxD, hxS] at hvalue
    exact Iff.intro (fun hx ↦ (hxS hx).elim) (fun hx ↦ (hxD hx).elim)

/-- Helper for Example 15 29: the conjugate domain of the packaged support owner is exactly the
underlying closed convex set. -/
private lemma effectiveDomain_supportOwnerConjugate_eq_set_local
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) (hD_nonempty : D.Nonempty) :
    effectiveDomain
      ((properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty))∗[
        supportFunction_mem_gammaZero_local D hD_nonempty]) = D := by
  let G : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  have hG : G ∈ Γ₀(K) := by
    -- Package the support owner once so the conjugate-domain rewrite is a single theorem.
    simpa [G] using supportFunction_mem_gammaZero_local D hD_nonempty
  have hGph : PositivelyHomogeneous G.asEReal := by
    -- The support owner inherits positive homogeneity from the support function.
    simpa [G] using supportFunction_positivelyHomogeneous_local D
  have hG0 : (G 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hGph hG
  have hconj :
      G.asEReal∗ = (ι[linearMinorantSet G]).asEReal :=
    conjugate_eq_indicator_linearMinorantSet_of_value_zero_of_positivelyHomogeneous hG0 hGph
  -- Rewrite the conjugate to an indicator once, then collapse the linear-minorant set back to `D`.
  calc
    effectiveDomain (G∗[hG]) = linearMinorantSet G := by
      ext u
      rw [mem_effectiveDomain_iff, gammaZeroConjugate_apply, hconj]
      by_cases hu : u ∈ linearMinorantSet G <;> simp [indicator_apply, hu]
    _ = D := by
      simpa [G] using
        linearMinorantSet_supportFunction_eq_set_local D hD_closed hD_convex hD_nonempty

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: infimal postcomposition of an indicator is exactly the indicator of
the image set. -/
private lemma infimalPostcomposition_indicator_eq_indicator_image_local
    (C : Set H) (L : H →L[ℝ] K) :
    L ▷ ι[C] = fun y : K ↦ ((ι[L '' C] y : Set.Ioi (⊥ : EReal)) : EReal) := by
  funext y
  by_cases hy : y ∈ L '' C
  · rcases hy with ⟨x, hxC, rfl⟩
    suffices hvalue : (L ▷ ι[C]) (L x) = 0 by
      have hyImage : L x ∈ L '' C := ⟨x, hxC, rfl⟩
      simpa [ERealFunction.indicator_apply, hyImage] using hvalue
    apply le_antisymm
    · -- A concrete feasible preimage already forces the fiberwise infimum down to `0`.
      change
        sInf (((fun z ↦ ((ι[C] z : Set.Ioi (⊥ : EReal)) : EReal)) '' (((L : H → K)) ⁻¹' {L x}))) ≤ 0
      exact sInf_le ⟨x, by simp, by simp [ERealFunction.indicator_apply, hxC]⟩
    · -- Every value on the fiber is at least `0`, so the infimum cannot drop below `0`.
      change
        0 ≤
          sInf
            ((fun z ↦ ((ι[C] z : Set.Ioi (⊥ : EReal)) : EReal)) '' (((L : H → K)) ⁻¹' {L x}))
      refine le_sInf ?_
      rintro _ ⟨z, hz, rfl⟩
      by_cases hzC : z ∈ C <;> simp [ERealFunction.indicator_apply, hzC]
  · suffices hvalue : (L ▷ ι[C]) y = ⊤ by
      simpa [ERealFunction.indicator_apply, hy] using hvalue
    apply le_antisymm le_top ?_
    -- Outside the image, every fiber point violates `x ∈ C`, so the infimum is `⊤`.
    change
      ⊤ ≤
        sInf
          ((fun z ↦ ((ι[C] z : Set.Ioi (⊥ : EReal)) : EReal)) '' (((L : H → K)) ⁻¹' {y}))
    refine le_sInf ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxC : x ∉ C := by
      intro hxC
      exact hy ⟨x, hxC, by simpa [Set.mem_preimage, Set.mem_singleton_iff] using hx⟩
    simp [ERealFunction.indicator_apply, hxC]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: the infimal postcomposition of an indicator is automatically
proper, since it only takes the values `0` and `⊤`. -/
private lemma infimalPostcomposition_indicator_isProper_local
    (C : Set H) (hC_nonempty : C.Nonempty) (L : H →L[ℝ] K) :
    IsProper (L ▷ ι[C]) := by
  refine ⟨?_, ?_⟩
  · intro y
    rw [infimalPostcomposition_indicator_eq_indicator_image_local]
    by_cases hy : y ∈ L '' C <;> simp [ERealFunction.indicator_apply, hy]
  · rcases hC_nonempty with ⟨x, hx⟩
    refine ⟨L x, ?_⟩
    rw [mem_dom_iff, infimalPostcomposition_indicator_eq_indicator_image_local]
    have hxImage : L x ∈ L '' C := ⟨x, hx, rfl⟩
    simp [ERealFunction.indicator_apply, hxImage]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: packaging the infimal postcomposition of an indicator does not
change its effective domain, which is exactly the image set. -/
private lemma effectiveDomain_infimalPostcompositionIndicator_eq_image_local
    (C : Set H) (hC_nonempty : C.Nonempty) (L : H →L[ℝ] K) :
    effectiveDomain
      (properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)) =
        L '' C := by
  ext y
  rw [mem_effectiveDomain_iff, properIoi_apply,
    infimalPostcomposition_indicator_eq_indicator_image_local]
  by_cases hy : y ∈ L '' C <;> simp [ERealFunction.indicator_apply, hy]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: after packaging the infimal postcomposition of an indicator, the
same-space owner is literally the indicator of the image. -/
private lemma properIoi_infimalPostcomposition_indicator_eq_indicator_image_local
    (C : Set H) (hC_nonempty : C.Nonempty) (L : H →L[ℝ] K) :
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L) =
      ι[L '' C] := by
  funext y
  apply Subtype.ext
  exact congrFun (infimalPostcomposition_indicator_eq_indicator_image_local C L) y

/-- Helper for Example 15 29: the primal owner `ι[S]` infimizes `g` exactly over the feasible
set `S`. -/
private lemma primalOptimalValue_indicator_eq_sInf_image_local
    (S : Set K) (g : K → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue (ι[S]) g = sInf (g.asEReal '' S) := by
  let primalRange : Set EReal := Set.range (primalObjective (ι[S]) g)
  let feasibleValues : Set EReal := g.asEReal '' S
  rw [primalOptimalValue_def]
  change sInf primalRange = sInf feasibleValues
  apply le_antisymm
  · refine (isGLB_sInf feasibleValues).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle : sInf primalRange ≤ primalObjective (ι[S]) g x :=
      (isGLB_sInf primalRange).1 (Set.mem_range_self x)
    simpa [primalRange, feasibleValues, primalObjective_apply, hx] using hle
  · refine (isGLB_sInf primalRange).2 ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ S
    · have hle : sInf feasibleValues ≤ (g x : EReal) :=
        (isGLB_sInf feasibleValues).1 ⟨x, hx, rfl⟩
      simpa [primalRange, feasibleValues, primalObjective_apply, hx] using hle
    · have hg_ne_bot : (g x : EReal) ≠ ⊥ := ne_of_gt (g x).2
      have htop : primalObjective (ι[S]) g x = ⊤ := by
        simp [primalObjective_apply, hx, EReal.top_add_of_ne_bot hg_ne_bot]
      rw [htop]
      exact le_top

/-- Helper for Example 15 29: the primal owner with first summand `ι[L '' C]` is the same
infimum as the original composite primal problem. -/
private lemma primalOptimalValue_indicatorImage_eq_composite_local
    (C : Set H) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    primalOptimalValue (ι[L '' C]) g = compositePrimalOptimalValue (ι[C]) g L := by
  -- Both owners infimize the same set of feasible values, just indexed by `L '' C` or by `C`.
  calc
    primalOptimalValue (ι[L '' C]) g =
        sInf (g.asEReal '' (L '' C)) := by
          exact primalOptimalValue_indicator_eq_sInf_image_local (L '' C) g
    _ = sInf ((fun x : H ↦ (g (L x) : EReal)) '' C) := by
          congr 1
          ext a
          constructor
          · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
            exact ⟨x, hx, rfl⟩
          · rintro ⟨x, hx, rfl⟩
            exact ⟨L x, ⟨x, hx, rfl⟩, rfl⟩
    _ = compositePrimalOptimalValue (ι[C]) g L := by
          simpa [compositePrimalOptimalValue, Function.comp] using
            (primalOptimalValue_indicator_eq_sInf_image_local C (g ∘ L)).symm

/-- Helper for Example 15 29: the composite dual owner is the same-space Fenchel dual owner for
the packaged infimal postcomposition. -/
private lemma compositeDualObjective_eq_fenchelDualObjective_infimalPostcomposition_local
    (f : H → Set.Ioi (⊥ : EReal))
    (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K)
    (hproper : IsProper (L ▷ f)) :
    compositeDualObjective f g L = fenchelDualObjective (properIoi (L ▷ f) hproper) g := by
  -- The Chapter 13 conjugation formula is the only bridge needed between the two owner spellings.
  funext v
  rw [compositeDualObjective_apply, fenchelDualObjective_apply,
    conjugate_infimalPostcomposition_eq_comp_adjoint]
  simp

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: membership of `0` in `sri (D - L '' C)` already forces both
constraint sets to be nonempty. -/
lemma nonempty_of_zero_mem_sri_sub_image
    (C : Set H) (D : Set K) (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (D - L '' C)) :
    C.Nonempty ∧ D.Nonempty := by
  -- Membership in `sri (D - L '' C)` first gives actual membership in the difference set.
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨y, hy, Lx, hLx, _⟩
  rcases hLx with ⟨x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩

omit [CompleteSpace H] in
/-- Helper for Example 15 29: the inner infimum over a nonempty set is never `⊤`. -/
lemma innerInfimumOn_ne_top_of_nonempty
    (C : Set H) (hC_nonempty : C.Nonempty) (u : H) :
    innerInfimumOn C u ≠ ⊤ := by
  rcases hC_nonempty with ⟨x, hx⟩
  -- A concrete feasible point gives a finite upper bound on the infimum.
  rw [innerInfimumOn_eq_sInf_image]
  exact ne_top_of_le_ne_top (by simp) (sInf_le ⟨x, hx, rfl⟩)

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: the composite primal value with an indicator constraint is the
infimum of the pulled-back objective on the feasible set. -/
lemma compositePrimalOptimalValue_indicator_eq_sInf_image
    (C : Set H) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    compositePrimalOptimalValue (ι[C]) g L =
      sInf ((fun x : H ↦ (g (L x) : EReal)) '' C) := by
  let primalRange : Set EReal := Set.range (compositePrimalObjective (ι[C]) g L)
  let feasibleValues : Set EReal := (fun x : H ↦ (g (L x) : EReal)) '' C
  -- The primal owner range differs from the feasible image only by possible `⊤` values outside
  -- `C`, so both infima coincide.
  rw [compositePrimalOptimalValue_def]
  change sInf primalRange = sInf feasibleValues
  apply le_antisymm
  · refine (isGLB_sInf feasibleValues).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    have hle : sInf primalRange ≤ compositePrimalObjective (ι[C]) g L x :=
      (isGLB_sInf primalRange).1 (Set.mem_range_self x)
    simpa [primalRange, feasibleValues, compositePrimalObjective_apply, hx] using hle
  · refine (isGLB_sInf primalRange).2 ?_
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ C
    · have hle : sInf feasibleValues ≤ (g (L x) : EReal) :=
        (isGLB_sInf feasibleValues).1 ⟨x, hx, rfl⟩
      simpa [primalRange, feasibleValues, compositePrimalObjective_apply, hx] using hle
    · have hg_ne_bot : (g (L x) : EReal) ≠ ⊥ := ne_of_gt (g (L x)).2
      have htop : compositePrimalObjective (ι[C]) g L x = ⊤ := by
        simp [compositePrimalObjective_apply, hx, EReal.top_add_of_ne_bot hg_ne_bot]
      rw [htop]
      exact le_top

/-- Helper for Example 15 29: the dual composite objective for the indicator of `C` is the
negative inner infimum plus the conjugate of the second term. -/
lemma compositeDualObjective_indicator_eq_neg_innerInfimum_add_conjugate
    (C : Set H) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (w : K) :
    compositeDualObjective (ι[C]) g L w =
      -(innerInfimumOn C (L.adjoint w)) + g.asEReal∗ w := by
  -- Rewrite the indicator conjugate as a support function and then convert that support term to
  -- the negative inner infimum.
  rw [compositeDualObjective_apply]
  have hindicator :
      ((ι[C]).asEReal)∗ (-(L.adjoint w)) = -(innerInfimumOn C (L.adjoint w)) := by
    calc
      ((ι[C]).asEReal)∗ (-(L.adjoint w))
          = σ[C] (-(L.adjoint w)) := by
              simpa using congrFun (conjugate_indicator_eq_supportFunction C) (-(L.adjoint w))
      _ = -(innerInfimumOn C (L.adjoint w)) := by
            simp [innerInfimumOn_eq_neg_supportFunction_neg]
  rw [hindicator]

/-- Helper for Example 15 29: for closed convex `D`, the dual objective with
`g = properIoi (σ[D]) ...` rewrites to the indicator-augmented negative inner infimum. -/
lemma compositeDualObjective_indicator_support_eq_neg_innerInfimum_add_indicator
    (C : Set H)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K) (w : K) :
    compositeDualObjective
        (ι[C])
        (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty))
        L w =
      -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal) := by
  -- First expose the generic indicator/composite-dual formula.
  rw [compositeDualObjective_indicator_eq_neg_innerInfimum_add_conjugate]
  have hD_gamma : ι[D] ∈ Γ₀(K) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
      D hD_nonempty hD_closed hD_convex
  have hsupport_conj :
      (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)).asEReal∗ =
        (ι[D]).asEReal := by
    calc
      (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)).asEReal∗
          = (σ[D])∗ := by
              rfl
      _ = (((ι[D]).asEReal)∗)∗ := by
            rw [← conjugate_indicator_eq_supportFunction D]
      _ = (ι[D]).asEReal := by
            simpa using biconjugate_eq_of_mem_gammaZero hD_gamma
  have hw :
      (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)).asEReal∗ w =
        (ι[D] w : EReal) := by
    simpa using congrFun hsupport_conj w
  rw [hw]

/-- Helper for Example 15 29: any global minimizer of the indicator-augmented dual objective that
already lies in `D` is a maximizer of the inner-infimum functional on `D`. -/
lemma isMaxOn_innerInfimum_of_mem_argmin_indicatorizedDual
    (C : Set H) (D : Set K) (L : H →L[ℝ] K) {v : K}
    (hvD : v ∈ D)
    (hvArg :
      v ∈ Argmin
        (fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal))) :
    IsMaxOn (fun w : K ↦ innerInfimumOn C (L.adjoint w)) D v := by
  -- On the feasible set `D`, the indicatorized dual objective is just the negative of the
  -- inner-infimum functional, so global minimization becomes constrained maximization.
  rw [isMaxOn_iff]
  have hvMin : IsMinOn
      (fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal))
      Set.univ v := by
    exact (mem_argmin_iff.mp hvArg)
  intro w hwD
  have hcompare :
      (fun u : K ↦ -(innerInfimumOn C (L.adjoint u)) + (ι[D] u : EReal)) v ≤
        (fun u : K ↦ -(innerInfimumOn C (L.adjoint u)) + (ι[D] u : EReal)) w :=
    (isMinOn_iff.mp hvMin) w (by simp)
  have hneg :
      -(innerInfimumOn C (L.adjoint v)) ≤ -(innerInfimumOn C (L.adjoint w)) := by
    simpa [hvD, hwD] using hcompare
  exact EReal.neg_le_neg_iff.mp hneg

/-- Helper for Example 15 29: if a global minimizer of the indicator-augmented dual objective
falls outside `D`, then every feasible point is also a global minimizer because all values are
forced to be `⊤`. -/
lemma exists_mem_D_mem_argmin_indicatorizedDual
    (C : Set H) (hC_nonempty : C.Nonempty)
    (D : Set K) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K) {v : K}
    (hvArg :
      v ∈ Argmin
        (fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal))) :
    ∃ w ∈ D,
      w ∈ Argmin
        (fun u : K ↦ -(innerInfimumOn C (L.adjoint u)) + (ι[D] u : EReal)) := by
  let dualObj : K → EReal := fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal)
  by_cases hvD : v ∈ D
  · -- A feasible global minimizer is already the desired witness.
    exact ⟨v, hvD, hvArg⟩
  · obtain ⟨d0, hd0⟩ := hD_nonempty
    have hvMin : IsMinOn dualObj Set.univ v := by
      exact (mem_argmin_iff.mp hvArg)
    have hinner_v_ne_top : innerInfimumOn C (L.adjoint v) ≠ ⊤ :=
      innerInfimumOn_ne_top_of_nonempty C hC_nonempty (L.adjoint v)
    have hneg_ne_bot : -(innerInfimumOn C (L.adjoint v)) ≠ ⊥ := by
      intro hbot
      apply hinner_v_ne_top
      simpa using congrArg Neg.neg hbot
    have hv_top : dualObj v = ⊤ := by
      simp [dualObj, hvD, EReal.add_top_of_ne_bot hneg_ne_bot]
    have htop_all : ∀ w : K, dualObj w = ⊤ := by
      intro w
      have hle : dualObj v ≤ dualObj w := (isMinOn_iff.mp hvMin) w (by simp)
      rw [hv_top] at hle
      exact top_le_iff.mp hle
    have hd0_arg : d0 ∈ Argmin dualObj := by
      rw [mem_argmin_iff, isMinOn_univ_iff]
      intro w
      rw [htop_all d0, htop_all w]
    exact ⟨d0, hd0, hd0_arg⟩

omit [CompleteSpace H] in
/-- Helper for Example 15 29: the source regularity hypothesis already has the exact Chapter 15
zero-shift shape once the support-side minorant set and the indicator domain are rewritten back to
`D` and `C`. -/
private lemma zero_mem_sri_linearMinorantSet_support_sub_image_indicator_local
    (C : Set H)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (D - L '' C)) :
    (0 : K) ∈
      sri
        (linearMinorantSet
            (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)) -
          L '' effectiveDomain (ι[C])) := by
  -- The support owner has `D` as its linear-minorant set, and the indicator owner has domain `C`.
  simpa [effectiveDomain_indicator,
    linearMinorantSet_supportFunction_eq_set_local D hD_closed hD_convex hD_nonempty] using hsri

omit [CompleteSpace H] in
/-- Helper for Example 15 29: after packaging the image indicator and support owner, the
support-side regularity surface is still exactly `D - L '' C`. -/
private lemma supportSurface_indicatorizedDual_eq_sub_image_local
    (C : Set H) (hC_nonempty : C.Nonempty)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hgD :
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty) ∈ Γ₀(K)) :
    let p : K → Set.Ioi (⊥ : EReal) :=
      properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
    effectiveDomain
        ((properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty))∗[hgD]) -
      effectiveDomain p = D - L '' C := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  -- Freeze the two domain rewrites once so later support-side arguments can stay on the textbook
  -- difference set `D - L '' C`.
  calc
    effectiveDomain
        ((properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty))∗[hgD]) -
        effectiveDomain p =
      D - effectiveDomain p := by
        rw [effectiveDomain_supportOwnerConjugate_eq_set_local D hD_closed hD_convex hD_nonempty]
    _ = D - L '' C := by
        rw [effectiveDomain_infimalPostcompositionIndicator_eq_image_local C hC_nonempty L]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Example 15 29: evaluating the conjugate of the composite primal owner at `0`
recovers the negative primal optimal value. -/
private lemma compositePrimalConjugate_zero_eq_neg_compositePrimalOptimalValue_local
    (F : H → Set.Ioi (⊥ : EReal)) (G : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    (compositePrimalObjective F G L)∗ (0 : H) = -compositePrimalOptimalValue F G L := by
  -- This is the canonical conjugate-at-zero identity specialized to the Chapter 15 owner.
  rw [conjugate_zero_eq_neg_iInf, compositePrimalOptimalValue_def, sInf_range]

/-- Helper for Example 15 29: positive homogeneity identifies the second conjugate term in the
composite dual objective with the indicator of the linear-minorant set. -/
private lemma compositeDualObjective_eq_add_indicator_linearMinorantSet_local
    (F : H → Set.Ioi (⊥ : EReal)) (G : K → Set.Ioi (⊥ : EReal))
    (hG : G ∈ Γ₀(K)) (hGph : PositivelyHomogeneous G.asEReal)
    (L : H →L[ℝ] K) (w : K) :
    compositeDualObjective F G L w =
      F.asEReal∗ (-(L.adjoint w)) + (ι[linearMinorantSet G] w : EReal) := by
  -- First rewrite `G∗` once through the Chapter 14 linear-minorant-set API.
  have hG0 : (G 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hGph hG
  have hconj :
      G.asEReal∗ = (ι[linearMinorantSet G]).asEReal :=
    conjugate_eq_indicator_linearMinorantSet_of_value_zero_of_positivelyHomogeneous hG0 hGph
  have hw :
      G.asEReal∗ w = (ι[linearMinorantSet G] w : EReal) := by
    simpa using congrFun hconj w
  -- The composite dual owner is now a single directed rewrite.
  rw [compositeDualObjective_apply, hw]

/-- Helper for Example 15 29: a positively homogeneous `Γ₀` function is the support function of
its linear-minorant set, and the conjugate domain is exactly that support surface. -/
private lemma supportSurfaceData_of_positivelyHomogeneous_mem_gammaZero_local
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (hph : PositivelyHomogeneous g.asEReal) :
    g.asEReal = σ[linearMinorantSet g] ∧
      effectiveDomain (g∗[hg]) = linearMinorantSet g ∧
      (linearMinorantSet g).Nonempty ∧
      IsClosed (linearMinorantSet g) ∧
      Convex ℝ (linearMinorantSet g) := by
  obtain ⟨hsupport, hnonempty, hclosed, hconvex⟩ :=
    supportFunction_linearMinorantSet_data_of_positivelyHomogeneous_mem_gammaZero hph hg
  have h0 : (g 0 : EReal) = 0 :=
    value_zero_eq_zero_of_positivelyHomogeneous_mem_gammaZero hph hg
  have hconj :
      g.asEReal∗ = (ι[linearMinorantSet g]).asEReal :=
    conjugate_eq_indicator_linearMinorantSet_of_value_zero_of_positivelyHomogeneous h0 hph
  have hdom :
      effectiveDomain (g∗[hg]) = linearMinorantSet g := by
    -- Rewrite the conjugate once to the indicator of the support surface.
    ext u
    rw [mem_effectiveDomain_iff, gammaZeroConjugate_apply, hconj]
    by_cases hu : u ∈ linearMinorantSet g <;> simp [indicator_apply, hu]
  exact ⟨hsupport, hdom, hnonempty, hclosed, hconvex⟩

/-- Helper for Example 15 29: the source regularity hypothesis already gives the closed-span core
condition on the subtype preimage of `D - L '' C`. -/
private lemma supportSurfaceCoreOnClosedSpan
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (D - L '' C)) :
    let Sdom : Set K := effectiveDomain (ι[D]) - L '' effectiveDomain (ι[C])
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ Sdom).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' Sdom)
    (0 : (B : Submodule ℝ K)) ∈ Set.core T := by
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
      C hC_nonempty hC_closed hC_convex
  have hD_gamma : ι[D] ∈ Γ₀(K) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
      D hD_nonempty hD_closed hD_convex
  have hsurface :
      effectiveDomain (ι[D]) - L '' effectiveDomain (ι[C]) = D - L '' C := by
    simp [effectiveDomain_indicator]
  have hsri_indicator :
      (0 : K) ∈ sri (effectiveDomain (ι[D]) - L '' effectiveDomain (ι[C])) := by
    simpa [hsurface] using hsri
  -- The indicator pair has exactly the textbook regularity surface `D - L '' C`.
  exact
    (restricted_zero_mem_core_subtype_preimage_on_closed_span
      (ι[C]) hC_gamma (ι[D]) hD_gamma L hsri_indicator)

/-- Helper for Example 15 29: normalize the closed-span core witness to the literal support
surface `D - L '' C` before introducing any dependent closed-span carrier. -/
private lemma supportSurfaceCoreOnExactSurface_local
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (D - L '' C)) :
    let Sdom : Set K := D - L '' C
    let B : ClosedSubmodule ℝ K :=
      ⟨(Submodule.span ℝ Sdom).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
    let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' Sdom)
    (0 : (B : Submodule ℝ K)) ∈ Set.core T := by
  -- Route correction: freeze the exact surface first so later users do not transport a core
  -- witness across two different dependent closed-span carriers.
  have hsurface :
      effectiveDomain (ι[D]) - L '' effectiveDomain (ι[C]) = D - L '' C := by
    simp [effectiveDomain_indicator]
  rw [← hsurface]
  exact
    supportSurfaceCoreOnClosedSpan
      C hC_closed hC_convex D hD_closed hD_convex hC_nonempty hD_nonempty L hsri

/-- Helper for Example 15 29: the raw infimal-postcomposition owner has the same primal value as
the source support-function infimum over `C`. -/
private lemma primalOptimalValue_infimalPostcomposition_indicator_support_eq_sInf_image_local
    (C : Set H) (hC_nonempty : C.Nonempty)
    (D : Set K) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K) :
    let p : K → Set.Ioi (⊥ : EReal) :=
      properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
    let gD : K → Set.Ioi (⊥ : EReal) :=
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    primalOptimalValue p gD = sInf ((fun x : H ↦ σ[D] (L x)) '' C) := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  -- First package the infimal postcomposition as the indicator of `L '' C`.
  calc
    primalOptimalValue p gD = primalOptimalValue (ι[L '' C]) gD := by
      rw [show p = ι[L '' C] by
        simpa [p] using
          properIoi_infimalPostcomposition_indicator_eq_indicator_image_local C hC_nonempty L]
    _ = compositePrimalOptimalValue (ι[C]) gD L := by
      simpa using primalOptimalValue_indicatorImage_eq_composite_local C gD L
    _ = sInf ((fun x : H ↦ σ[D] (L x)) '' C) := by
      simpa [gD] using compositePrimalOptimalValue_indicator_eq_sInf_image C gD L

/-- Helper for Example 15 29: the raw same-space dual owner for the infimal postcomposition
specialization is already the source-facing indicatorized dual objective. -/
private lemma fenchelDualObjective_infimalPostcomposition_indicator_support_eq_indicatorizedDual_local
    (C : Set H) (hC_nonempty : C.Nonempty)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K) (w : K) :
    let p : K → Set.Ioi (⊥ : EReal) :=
      properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
    let gD : K → Set.Ioi (⊥ : EReal) :=
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    fenchelDualObjective p gD w =
      -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal) := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  have hdual :
      compositeDualObjective (ι[C]) gD L = fenchelDualObjective p gD := by
    -- Freeze the infimal-postcomposition rewrite before translating the support-side objective.
    simpa [p] using
      compositeDualObjective_eq_fenchelDualObjective_infimalPostcomposition_local
        (ι[C]) gD L
        (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  calc
    fenchelDualObjective p gD w = compositeDualObjective (ι[C]) gD L w := by
      simpa using (congrFun hdual w).symm
    _ = -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal) := by
      -- Then rewrite the support-side composite owner to the indicatorized source formula.
      simpa [gD] using
        compositeDualObjective_indicator_support_eq_neg_innerInfimum_add_indicator
          C D hD_closed hD_convex hD_nonempty L w

/-- Helper for Example 15 29: package the concrete support-side regularity data for the
indicatorized dual route. -/
private lemma supportRegularityBundle_indicatorizedDual_local
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (D - L '' C)) :
    let p : K → Set.Ioi (⊥ : EReal) :=
      properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
    let gD : K → Set.Ioi (⊥ : EReal) :=
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    ∃ hgD : gD ∈ Γ₀(K),
      PositivelyHomogeneous gD.asEReal ∧
      effectiveDomain (gD∗[hgD]) = D ∧
      effectiveDomain p = L '' C ∧
      let Sdom : Set K := effectiveDomain (gD∗[hgD]) - effectiveDomain p
      let B : ClosedSubmodule ℝ K :=
        ⟨(Submodule.span ℝ Sdom).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
      let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' Sdom)
      (0 : (B : Submodule ℝ K)) ∈ Set.core T := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  have hgD : gD ∈ Γ₀(K) := by
    -- The support owner is the canonical `Γ₀` object on the dual side.
    simpa [gD] using supportFunction_mem_gammaZero_local D hD_nonempty
  have hG_ph : PositivelyHomogeneous gD.asEReal := by
    -- Positive homogeneity exposes the support surface `D` through the conjugate domain.
    simpa [gD] using supportFunction_positivelyHomogeneous_local D
  have hdom_conj : effectiveDomain (gD∗[hgD]) = D := by
    -- The conjugate of the packaged support function is exactly the indicator of `D`.
    simpa [gD] using
      effectiveDomain_supportOwnerConjugate_eq_set_local D hD_closed hD_convex hD_nonempty
  have hdom_p : effectiveDomain p = L '' C := by
    -- The infimal postcomposition owner is just the indicator of the image set.
    simpa [p] using
      effectiveDomain_infimalPostcompositionIndicator_eq_image_local C hC_nonempty L
  have hcore_support :
      let Sdom : Set K := effectiveDomain (gD∗[hgD]) - effectiveDomain p
      let B : ClosedSubmodule ℝ K :=
        ⟨(Submodule.span ℝ Sdom).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
      let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' Sdom)
      (0 : (B : Submodule ℝ K)) ∈ Set.core T := by
    have hsurface :
        effectiveDomain (gD∗[hgD]) - effectiveDomain p = D - L '' C := by
      -- Freeze the support-side surface in the textbook spelling before forming the subtype.
      simpa [p] using
        supportSurface_indicatorizedDual_eq_sub_image_local
          C hC_nonempty D hD_closed hD_convex hD_nonempty L hgD
    rw [hsurface]
    -- The exact-surface core lemma now matches the bundled support surface after one rewrite.
    exact
      supportSurfaceCoreOnExactSurface_local
        C hC_closed hC_convex D hD_closed hD_convex hC_nonempty hD_nonempty L hsri
  exact ⟨hgD, hG_ph, hdom_conj, hdom_p, hcore_support⟩

/-- Helper for Example 15 29: the product-graph canonical slice `(L.adjoint w, -w)` already
rewrites the support-side graph dual objective to the normalized same-space Fenchel dual owner. -/
private lemma supportCanonicalSliceFenchelDual_eq_local
    (C : Set H) (hC_nonempty : C.Nonempty)
    (D : Set K) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K) (w : K) :
    let p : K → Set.Ioi (⊥ : EReal) :=
      properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
    let gD : K → Set.Ioi (⊥ : EReal) :=
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    fenchelDualObjective
        ((fun q : H × K ↦ (ι[C]) q.1) + fun q ↦ gD q.2)
        (ι[(L.toLinearMap.graph : Set (H × K))])
        (L.adjoint w, -w) =
      fenchelDualObjective p gD w := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  have hdual :
      compositeDualObjective (ι[C]) gD L = fenchelDualObjective p gD := by
    -- Freeze the infimal-postcomposition rewrite before comparing it with the product-graph
    -- canonical slice.
    simpa [p] using
      compositeDualObjective_eq_fenchelDualObjective_infimalPostcomposition_local
        (ι[C]) gD L
        (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  calc
    fenchelDualObjective
        ((fun q : H × K ↦ (ι[C]) q.1) + fun q ↦ gD q.2)
        (ι[(L.toLinearMap.graph : Set (H × K))])
        (L.adjoint w, -w) =
      compositeDualObjective (ι[C]) gD L w := by
        simpa using
          fenchelDualObjective_product_graph_eq_compositeDualObjective_on_adjoint_neg
            (ι[C]) gD L w
    _ = fenchelDualObjective p gD w := by
      simpa using congrFun hdual w

/-- Helper for Example 15 29: the closed-span subtype core witness on the normalized support
surface already upgrades to the ambient strong-relative-interior hypothesis on that same surface.
-/
private lemma zero_mem_sri_supportSurface_of_zero_mem_core_subtype_preimage_local
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (hC_nonempty : C.Nonempty)
    (gD : K → Set.Ioi (⊥ : EReal))
    (hgD : gD ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hcore_support :
      let Sdom : Set K := effectiveDomain (gD∗[hgD]) - L '' effectiveDomain (ι[C])
      let B : ClosedSubmodule ℝ K :=
        ⟨(Submodule.span ℝ Sdom).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
      let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' Sdom)
      (0 : (B : Submodule ℝ K)) ∈ Set.core T) :
    (0 : K) ∈ sri (effectiveDomain (gD∗[hgD]) - L '' effectiveDomain (ι[C])) := by
  let Sdom : Set K := effectiveDomain (gD∗[hgD]) - L '' effectiveDomain (ι[C])
  let B : ClosedSubmodule ℝ K :=
    ⟨(Submodule.span ℝ Sdom).topologicalClosure, Submodule.isClosed_topologicalClosure _⟩
  let T : Set (B : Submodule ℝ K) := ((↑) ⁻¹' Sdom)
  let B0 : Submodule ℝ K := (B : Submodule ℝ K)
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
      C hC_nonempty hC_closed hC_convex
  have hgD_conj : (gD∗[hgD]) ∈ Γ₀(K) :=
    gammaZeroConjugate_mem_gammaZero hgD
  have h0T : (0 : B0) ∈ T := (Set.mem_core_iff.mp hcore_support).1
  have h0Sdom : (0 : K) ∈ Sdom := by
    -- Unpack the subtype origin witness back to the ambient support surface.
    simpa [T, B0, Sdom] using h0T
  have hSdom_nonempty : Sdom.Nonempty := ⟨0, h0Sdom⟩
  have hSdom_convex : Convex ℝ Sdom := by
    -- The support surface is the difference of two convex effective domains.
    dsimp [Sdom]
    exact
      hgD_conj.2.convex_effectiveDomain.sub
        (hC_gamma.2.convex_effectiveDomain.linear_image L.toLinearMap)
  have hTsub : T - ({(0 : B0)} : Set B0) = T := by
    -- Subtracting the subtype origin does not change the closed-span preimage.
    ext v
    constructor
    · rintro ⟨u, hu, w, hw, huw⟩
      rcases Set.mem_singleton_iff.mp hw with rfl
      have huv : u = v := by
        simpa using huw
      simpa [huv] using hu
    · intro hv
      exact Set.mem_sub.mpr ⟨v, hv, 0, by simp, by simp⟩
  have hconeT : cone T = (univ : Set B0) := by
    -- Read the core predicate through the Chapter 6 cone criterion on the subtype carrier.
    simpa [T, Sdom, hTsub, effectiveDomain_indicator] using (Set.mem_core_iff.mp hcore_support).2
  have hconeSdom :
      cone Sdom = (((Submodule.span ℝ Sdom).topologicalClosure : Submodule ℝ K) : Set K) := by
    apply Set.Subset.antisymm
    · -- Every ambient cone point lies in the closed span generated by the support surface.
      intro x hx
      exact cone_subset_topologicalClosure_span Sdom hx
    · intro x hx
      let xB : B0 := ⟨x, hx⟩
      have hxConeT : xB ∈ cone T := by
        -- The subtype cone fills the whole closed span.
        simpa [hconeT]
      -- Move from the closed-span subtype back to the literal ambient support surface.
      exact
        (mem_cone_subtype_preimage_sub_image_difference_iff
          (f := ι[C]) (hf := hC_gamma) (g := (gD∗[hgD])) (hg := hgD_conj) (L := L)).1 hxConeT
  -- The ambient support surface now satisfies the Chapter 6 `core -> sri` criterion.
  exact
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      hSdom_nonempty hSdom_convex).2 hconeSdom

/-- Helper for Example 15 29: once the support-side product-graph bridge is available, the
indicator/support composite dual owner attains its minimum. -/
private lemma
    exists_mem_argmin_compositeDualObjective_indicator_support_of_zero_mem_sri_sub_image_local
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (bar D - L '' C)) :
    let gD : K → Set.Ioi (⊥ : EReal) :=
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    ∃ u ∈ Argmin (compositeDualObjective (ι[C]) gD L),
      compositePrimalOptimalValue (ι[C]) gD L = -(compositeDualObjective (ι[C]) gD L u) := by
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  have hC_gamma : ι[C] ∈ Γ₀(H) :=
    indicatorMemGammaZeroOfNonemptyIsClosedConvexLocal
      C hC_nonempty hC_closed hC_convex
  have hgD : gD ∈ Γ₀(K) := by
    -- Route correction: the source regularity uses `bar D`, the actual support-function domain.
    simpa [gD] using supportFunction_mem_gammaZero_local D hD_nonempty
  have hsri_owner :
      (0 : K) ∈ sri (effectiveDomain gD - L '' effectiveDomain (ι[C])) := by
    -- Rewrite the source barrier-cone hypothesis to the owner regularity surface of Theorem 15.23.
    simpa [gD, effectiveDomain_indicator,
      effectiveDomain_supportOwner_eq_barrierCone_local D hD_nonempty hD_closed hD_convex] using hsri
  -- The composite dual owner now fits Theorem 15.23 exactly, with no graph-level detour.
  simpa [gD] using
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      (f := ι[C]) hC_gamma (g := gD) hgD (L := L) hsri_owner

/-- Helper for Example 15 29: the source regularity hypothesis already attains the same-space
Fenchel dual owner for the infimal-postcomposition/support pair. -/
private lemma
    exists_mem_argmin_fenchelDualObjective_infimalPostcomposition_indicator_support_of_zero_mem_sri_sub_image_local
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (bar D - L '' C)) :
    let p : K → Set.Ioi (⊥ : EReal) :=
      properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
    let gD : K → Set.Ioi (⊥ : EReal) :=
      properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
    ∃ u ∈ Argmin (fenchelDualObjective p gD),
      primalOptimalValue p gD = -(fenchelDualObjective p gD u) := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  have hdual :
      compositeDualObjective (ι[C]) gD L = fenchelDualObjective p gD := by
    -- Rewrite the composite owner to the same-space infimal-postcomposition owner once.
    simpa [p] using
      compositeDualObjective_eq_fenchelDualObjective_infimalPostcomposition_local
        (ι[C]) gD L
        (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  have hprimal :
      compositePrimalOptimalValue (ι[C]) gD L = primalOptimalValue p gD := by
    -- The infimal postcomposition of `ι[C]` is literally the indicator of `L '' C`.
    calc
      compositePrimalOptimalValue (ι[C]) gD L = primalOptimalValue (ι[L '' C]) gD := by
        symm
        simpa using primalOptimalValue_indicatorImage_eq_composite_local C gD L
      _ = primalOptimalValue p gD := by
        rw [show p = ι[L '' C] by
          simpa [p] using
            properIoi_infimalPostcomposition_indicator_eq_indicator_image_local
              C hC_nonempty L]
  obtain ⟨u, huArg, huEq⟩ :=
    exists_mem_argmin_compositeDualObjective_indicator_support_of_zero_mem_sri_sub_image_local
      C hC_closed hC_convex D hD_closed hD_convex hC_nonempty hD_nonempty L hsri
  refine ⟨u, ?_, ?_⟩
  · -- Transport the attained minimizer through the owner equality `compositeDualObjective = fenchelDualObjective`.
    have huMin : IsMinOn (compositeDualObjective (ι[C]) gD L) Set.univ u :=
      mem_argmin_iff.mp huArg
    rw [mem_argmin_iff]
    rw [isMinOn_iff] at huMin ⊢
    intro z hz
    convert huMin z hz using 1
    · simpa [p, gD] using (congrFun hdual u).symm
    · simpa [p, gD] using (congrFun hdual z).symm
  · -- Rewrite both the primal and dual owner values through the same normalization.
    calc
      primalOptimalValue p gD = compositePrimalOptimalValue (ι[C]) gD L := hprimal.symm
      _ = -(compositeDualObjective (ι[C]) gD L u) := huEq
      _ = -(fenchelDualObjective p gD u) := by
            rw [show compositeDualObjective (ι[C]) gD L u = fenchelDualObjective p gD u by
              simpa using congrFun hdual u]

/-- Helper for Example 15 29: the normalized indicatorized dual objective should attain its
minimum under the source regularity hypothesis `0 ∈ sri (bar D - L '' C)`. -/
private lemma exists_mem_argmin_indicatorizedDual_of_zero_mem_sri_sub_image
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (hC_nonempty : C.Nonempty) (hD_nonempty : D.Nonempty)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (bar D - L '' C)) :
    ∃ w ∈ Argmin
        (fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal)),
      compositePrimalOptimalValue
          (ι[C])
          (properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty))
          L =
        -((fun u : K ↦ -(innerInfimumOn C (L.adjoint u)) + (ι[D] u : EReal)) w) := by
  let p : K → Set.Ioi (⊥ : EReal) :=
    properIoi (L ▷ ι[C]) (infimalPostcomposition_indicator_isProper_local C hC_nonempty L)
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  let dualObj : K → EReal :=
    fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal)
  have hdual :
      fenchelDualObjective p gD = dualObj := by
    funext w
    -- Route correction: collapse the same-space support owner directly to the source objective.
    simpa [p, gD, dualObj] using
      fenchelDualObjective_infimalPostcomposition_indicator_support_eq_indicatorizedDual_local
        C hC_nonempty D hD_closed hD_convex hD_nonempty L w
  have hprimal :
      compositePrimalOptimalValue (ι[C]) gD L = primalOptimalValue p gD := by
    -- Reuse the same infimal-postcomposition normalization on the primal side.
    calc
      compositePrimalOptimalValue (ι[C]) gD L = primalOptimalValue (ι[L '' C]) gD := by
        symm
        simpa using primalOptimalValue_indicatorImage_eq_composite_local C gD L
      _ = primalOptimalValue p gD := by
        rw [show p = ι[L '' C] by
          simpa [p] using
            properIoi_infimalPostcomposition_indicator_eq_indicator_image_local
              C hC_nonempty L]
  obtain ⟨w, hwArg, hwEq⟩ :=
    exists_mem_argmin_fenchelDualObjective_infimalPostcomposition_indicator_support_of_zero_mem_sri_sub_image_local
      C hC_closed hC_convex D hD_closed hD_convex hC_nonempty hD_nonempty L hsri
  refine ⟨w, ?_, ?_⟩
  · -- Rewrite the same-space Fenchel minimizer as a minimizer of the explicit indicatorized dual.
    have hwMin : IsMinOn (fenchelDualObjective p gD) Set.univ w :=
      mem_argmin_iff.mp hwArg
    rw [mem_argmin_iff]
    rw [isMinOn_iff] at hwMin ⊢
    intro z hz
    convert hwMin z hz using 1
    · simpa [p, gD, dualObj] using (congrFun hdual w).symm
    · simpa [p, gD, dualObj] using (congrFun hdual z).symm
  · -- Translate the strong-duality value identity through the explicit objective formula.
    calc
      compositePrimalOptimalValue (ι[C]) gD L = primalOptimalValue p gD := hprimal
      _ = -(fenchelDualObjective p gD w) := hwEq
      _ = -(dualObj w) := by
            rw [show fenchelDualObjective p gD w = dualObj w by
              simpa using congrFun hdual w]

-- Proof sketch: apply Theorem 15.23 with `f = ι_C` and `g = σ[D]`, using Example 13.3(i) to
-- identify the conjugate of `ι_C` with `σ[C]` and Example 13.43(i) to identify the conjugate of
-- `σ[D]` with the indicator of the closed convex set `D`. The support-specific Chapter 15
-- consequence used later in the chapter is the value equality
-- `inf_{x ∈ C} σ[D](Lx) = max_{v ∈ D} innerInfimumOn C (L.adjoint v)`.
/-- Example 15.29: if `C ⊆ H` is closed convex, `D ⊆ K` is nonempty closed convex, and
`0 ∈ sri (bar D - L '' C)`, then the primal value
`inf_{x ∈ C} sup_{v ∈ D} ⟪Lx, v⟫` is attained as the dual value
`inf_{x ∈ C} ⟪Lx, v⟫` at some `v ∈ D` maximizing
`w ↦ inf_{x ∈ C} ⟪Lx, w⟫`, written here as
`sInf ((fun x ↦ σ[D] (L x)) '' C) = innerInfimumOn C (L.adjoint v)`.
The declaration name is kept for compatibility with the existing pipeline output. -/
theorem exists_dualMaximizer_inf_inner_eq_inf_supportFunction_of_zero_mem_sri_sub_image
    (C : Set H) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (D : Set K) (hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (bar D - L '' C)) :
    ∃ v ∈ D,
      IsMaxOn (fun w : K ↦ innerInfimumOn C (L.adjoint w)) D v ∧
        sInf ((fun x : H ↦ σ[D] (L x)) '' C) =
          innerInfimumOn C (L.adjoint v) := by
  let gD : K → Set.Ioi (⊥ : EReal) :=
    properIoi (σ[D]) (supportFunction_isProper_of_nonempty_local D hD_nonempty)
  let dualObj : K → EReal :=
    fun w : K ↦ -(innerInfimumOn C (L.adjoint w)) + (ι[D] w : EReal)
  have hC_nonempty : C.Nonempty :=
    (nonempty_of_zero_mem_sri_sub_image C (bar D) L hsri).1
  obtain ⟨w, hwArg, hwEq⟩ :=
    exists_mem_argmin_indicatorizedDual_of_zero_mem_sri_sub_image
      C hC_closed hC_convex D hD_closed hD_convex hC_nonempty hD_nonempty L hsri
  obtain ⟨v, hvD, hvArg⟩ :=
    exists_mem_D_mem_argmin_indicatorizedDual C hC_nonempty D hD_nonempty L hwArg
  have hvEq :
      compositePrimalOptimalValue (ι[C]) gD L = -(dualObj v) := by
    have hwVal : dualObj w = sInf (Set.range dualObj) :=
      mem_argmin_iff_eq_sInf.mp hwArg
    have hvVal : dualObj v = sInf (Set.range dualObj) :=
      mem_argmin_iff_eq_sInf.mp hvArg
    -- Any two global minimizers of the same objective share the same value.
    calc
      compositePrimalOptimalValue (ι[C]) gD L = -(dualObj w) := hwEq
      _ = -(dualObj v) := by rw [hwVal, hvVal]
  refine ⟨v, hvD, ?_, ?_⟩
  · -- A feasible global minimizer of the indicatorized dual is exactly a maximizer on `D`.
    exact isMaxOn_innerInfimum_of_mem_argmin_indicatorizedDual C D L hvD hvArg
  · -- Rewrite the primal owner to the source support-function infimum, then simplify feasibility.
    calc
      sInf ((fun x : H ↦ σ[D] (L x)) '' C) = compositePrimalOptimalValue (ι[C]) gD L := by
        symm
        simpa [gD] using compositePrimalOptimalValue_indicator_eq_sInf_image C gD L
      _ = -(dualObj v) := hvEq
      _ = innerInfimumOn C (L.adjoint v) := by
            simp [dualObj, hvD]

end FenchelRockafellarDuality

end ERealFunction
