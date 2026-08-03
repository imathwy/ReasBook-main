import Mathlib
import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap09.Proposition_9_30
import BauschkeLean.Chap12.Definition_12_1
import BauschkeLean.Chap12.Definition_12_34
import BauschkeLean.Chap12.Proposition_12_6
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap13.Corollary_13_38
import BauschkeLean.Chap13.Corollary_13_25
import BauschkeLean.Chap13.Proposition_13_48
import BauschkeLean.Chap15.Definition_15_19
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap16.Corollary_16_30
import BauschkeLean.Chap16.Definition_16_1
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap16.Proposition_16_10
import BauschkeLean.Chap16.Proposition_16_42
import BauschkeLean.Chap16.Proposition_16_60
import BauschkeLean.Chap16.Proposition_16_61
import BauschkeLean.Chap25.Definition_25_29
import BauschkeLean.Chap25.Definition_25_39

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise SetValuedOperator translate

noncomputable section

universe u v

namespace ERealFunction

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Proposition 25.43 records the Chapter 25 regularity and subdifferential
  formulas for `((L ▷ f) □ g)`.
- `core/canonical`: the function owners are Chapter 12 `infimalPostcomposition` / `□`, and the
  operator owners are Chapter 25 `parallelComposition` / `parallelSum`.
- `bridge/view`: Proposition 25.32 and Proposition 25.42 supply the matching function/operator
  calculus identities used downstream.
-/

variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
variable {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
variable (L : H →L[ℝ] K)
variable
  (hsri :
    (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - L.adjoint '' effectiveDomain (g∗[hg])))

/-- Helper for Proposition 25.43: the affine tilt of an `EReal`-valued function by the linear
term `x ↦ -⟪x, y⟫`. -/
private noncomputable def affineTiltEReal (φ : K → EReal) (y : K) : K → EReal :=
  fun x ↦ φ x + (((-⟪x, y⟫_ℝ : ℝ) : EReal))

/-- Helper for Proposition 25.43: evaluating the affine tilt exposes the added linear term. -/
@[simp] private theorem affineTiltEReal_apply
    (φ : K → EReal) (y x : K) :
    affineTiltEReal φ y x = φ x + (((-⟪x, y⟫_ℝ : ℝ) : EReal)) :=
  rfl

/-- Helper for Proposition 25.43: affine tilting a `Γ₀(K)` function preserves properness. -/
private theorem affine_tilt_isProper
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K)) (y : K) :
    IsProper (affineTiltEReal h.asEReal y) := by
  have htilt_eq_coe :
      ∀ ⦃x : K⦄, x ∈ effectiveDomain h →
        affineTiltEReal h.asEReal y x =
          (((h.asEReal x).toReal - ⟪x, y⟫_ℝ : ℝ) : EReal) := by
    intro x hx
    -- On the effective domain, the tilted value is a finite real-valued perturbation of `h x`.
    have hx_top : h.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : h.asEReal x ≠ ⊥ := ne_of_gt (h x).2
    rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  constructor
  · intro x
    by_cases hx : x ∈ effectiveDomain h
    · -- Inside the effective domain, the affine tilt is a finite real number.
      rw [htilt_eq_coe hx]
      exact EReal.coe_ne_bot _
    · -- Outside the effective domain, `h x = ⊤`, so the tilt stays at `⊤`.
      have hx_top : h.asEReal x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
      rw [affineTiltEReal, hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, y⟫_ℝ))]
      simp
  · rcases hh.2.nonempty with ⟨x, hx⟩
    -- A finite point of `h` remains finite after adding the linear perturbation.
    refine ⟨x, ?_⟩
    rw [mem_dom_iff, htilt_eq_coe hx]
    simpa using (EReal.coe_lt_top (((h.asEReal x).toReal - ⟪x, y⟫_ℝ : ℝ)))

/-- Helper for Proposition 25.43: package the affine tilt back into the `]-∞,+∞]` codomain used
by the Chapter 15 owners. -/
private noncomputable abbrev affineTiltIoi
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K)) (y : K) :
    K → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltEReal h.asEReal y) (affine_tilt_isProper h hh y)

/-- Helper for Proposition 25.43: coercing the packaged affine tilt back to `EReal` recovers the
raw tilted function. -/
@[simp] private theorem affineTiltIoi_apply
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K)) (y x : K) :
    (affineTiltIoi h hh y x : EReal) = affineTiltEReal h.asEReal y x := by
  rfl

/-- Helper for Proposition 25.43: the packaged affine tilt of a `Γ₀(K)` function still lies in
`Γ₀(K)`. -/
private theorem affine_tilt_mem_gammaZero
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K)) (y : K) :
    affineTiltIoi h hh y ∈ Γ₀(K) := by
  have hlinear_gamma :
      (fun x : K ↦ (((-⟪x, y⟫_ℝ : ℝ) : EReal))) ∈ Γ(K) := by
    rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · intro x z a ha0 ha1
      change (((-(⟪a • x + (1 - a) • z, y⟫_ℝ) : ℝ) : EReal)) ≤
        (a : EReal) * (((-⟪x, y⟫_ℝ : ℝ) : EReal)) +
          (1 - a : EReal) * (((-⟪z, y⟫_ℝ : ℝ) : EReal))
      have hreal :
          -(⟪a • x + (1 - a) • z, y⟫_ℝ) =
            a * (-⟪x, y⟫_ℝ) + (1 - a) * (-⟪z, y⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hsub : (1 - (a : EReal)) = (((1 - a : ℝ)) : EReal) := by
        norm_num
      rw [hreal, hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    · simpa using
        (continuous_coe_real_ereal.comp
          ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous
  have htilt_gamma : affineTiltEReal h.asEReal y ∈ Γ(K) := by
    have hh_gamma : h.asEReal ∈ Γ(K) := asEReal_mem_gamma_of_mem_gammaZero hh
    rw [mem_gamma_iff] at hh_gamma hlinear_gamma ⊢
    refine ⟨?_, ?_⟩
    · intro x z a ha0 ha1
      have haE_nonneg : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha0
      have hbE_nonneg : (0 : EReal) ≤ (1 - a : EReal) := by
        exact_mod_cast sub_nonneg.mpr ha1
      have haE_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
      have hbE_ne_top : (1 - a : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - a)
      calc
        affineTiltEReal h.asEReal y (a • x + (1 - a) • z)
            ≤ ((a : EReal) * h.asEReal x + (1 - a : EReal) * h.asEReal z) +
                ((a : EReal) * (((-⟪x, y⟫_ℝ : ℝ) : EReal)) +
                  (1 - a : EReal) * (((-⟪z, y⟫_ℝ : ℝ) : EReal))) := by
              simpa [affineTiltEReal] using
                add_le_add (hh_gamma.1 ha0 ha1) (hlinear_gamma.1 ha0 ha1)
        _ = (a : EReal) * affineTiltEReal h.asEReal y x +
              (1 - a : EReal) * affineTiltEReal h.asEReal y z := by
              simp [affineTiltEReal,
                EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hbE_nonneg hbE_ne_top,
                add_assoc, add_left_comm]
    · rw [lowerSemicontinuous_iff_le_liminf]
      intro x
      calc
        affineTiltEReal h.asEReal y x
            ≤ Filter.liminf h.asEReal (nhds x) +
                Filter.liminf (fun z : K ↦ (((-⟪z, y⟫_ℝ : ℝ) : EReal))) (nhds x) := by
              simpa [affineTiltEReal] using
                add_le_add (hh_gamma.2.le_liminf x) (hlinear_gamma.2.le_liminf x)
        _ ≤ Filter.liminf (affineTiltEReal h.asEReal y) (nhds x) := by
              simpa [affineTiltEReal] using
                (EReal.le_liminf_add :
                  Filter.liminf h.asEReal (nhds x) +
                      Filter.liminf
                        (fun z : K ↦ (((-⟪z, y⟫_ℝ : ℝ) : EReal)))
                        (nhds x) ≤
                    Filter.liminf
                      (fun z : K ↦
                        h.asEReal z + (((-⟪z, y⟫_ℝ : ℝ) : EReal)))
                      (nhds x))
  -- Package the raw tilted `Γ`-function back into the project `Γ₀` owner.
  exact properIoi_mem_gammaZero_of_mem_gamma (affine_tilt_isProper h hh y) htilt_gamma

/-- Helper for Proposition 25.43: affine tilting does not change the effective domain. -/
private theorem effectiveDomain_affineTiltIoi
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K)) (y : K) :
    effectiveDomain (affineTiltIoi h hh y) = effectiveDomain h := by
  ext x
  by_cases hx : x ∈ effectiveDomain h
  · have hx_top : h.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : h.asEReal x ≠ ⊥ := ne_of_gt (h x).2
    rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hvalue :
        affineTiltEReal h.asEReal y x =
          (((h.asEReal x).toReal - ⟪x, y⟫_ℝ : ℝ) : EReal) := by
      rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
      simp [sub_eq_add_neg]
    rw [affineTiltIoi_apply, hvalue]
    constructor
    · intro _
      exact mem_effectiveDomain_iff.mp hx
    · intro _
      exact EReal.coe_lt_top _
  · rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hx_top : h.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [affineTiltIoi_apply, affineTiltEReal, hx_top,
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, y⟫_ℝ))]
    simp [hx_top]

/-- Helper for Proposition 25.43: evaluating a conjugate at the origin rewrites it as the
negative of the indexed infimum. -/
private theorem conjugate_zero_eq_neg_iInf_local
    (φ : K → EReal) :
    φ∗ 0 = - (⨅ x : K, φ x) := by
  calc
    φ∗ 0 = ⨆ x : K, -φ x := by
      simp [conjugate_apply]
    _ = - (⨅ x : K, φ x) := by
      have hneg : (-(⨅ x : K, φ x) : EReal) = ⨆ x : K, -φ x := by
        exact OrderIso.map_iInf EReal.negOrderIso (fun x : K ↦ φ x)
      rw [hneg]

/-- Helper for Proposition 25.43: Fenchel conjugation of the packaged affine tilt translates the
conjugate by `-y`. -/
private theorem conjugate_affineTiltIoi
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K)) (y : K) :
    (affineTiltIoi h hh y).asEReal∗ = τ (-y) (h.asEReal∗) := by
  ext v
  have hconj :=
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := h.asEReal) (y := (0 : K)) (v := -y) (β := 0))
      v
  simpa [Function.asEReal_apply, affineTiltEReal, Pi.add_apply, add_assoc] using hconj

/-- Helper for Proposition 25.43: tilting the primal objective commutes with the composite owner.
-/
private theorem tilted_compositePrimalObjective_eq_affineTilt
    (h : K → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(K))
    (k : H → Set.Ioi (⊥ : EReal)) (A : K →L[ℝ] H) (y : K) :
    compositePrimalObjective (affineTiltIoi h hh y) k A =
      affineTiltEReal (compositePrimalObjective h k A) y := by
  funext x
  -- Expanding both owners shows the same pointwise affine perturbation.
  rw [compositePrimalObjective_apply, affineTiltIoi_apply, affineTiltEReal]
  simp [compositePrimalObjective_apply, add_assoc, add_left_comm, add_comm]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K] hf hg hsri in
/-- Helper for Proposition 25.43: precomposing a `Γ₀` function with a continuous linear map keeps
`Γ₀` membership once the range meets the effective domain. This is the small owner-free fragment of
the Chapter 15 precomposition API needed locally in this file. -/
private theorem precompContinuousLinearMapMemGammaZeroOfRangeInterEffectiveDomainNonempty
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (h : F → Set.Ioi (⊥ : EReal)) (hh : h ∈ Γ₀(F))
    (A : E →L[ℝ] F)
    (hdom : (Set.range A ∩ effectiveDomain h).Nonempty) :
    h ∘ A ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity survives precomposition by continuity of the linear map.
    simpa using hh.1.comp A.continuous
  · refine ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty h A hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : A x ∈ effectiveDomain h := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    have hy' : A y ∈ effectiveDomain h := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hy
    -- Push convexity through the linear map and reuse the original `Γ₀` inequality.
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hh.2.ineq hx' hy' hα hα_lt_one

include hf hg hsri

/- Helper for Proposition 25.43: adding a finite real shift commutes with `iInf` in `EReal`. -/
omit hf hg hsri in
private theorem ereal_iInf_add_of_real_shift
    {ι : Sort*} (r : ℝ) (φ : ι → EReal) :
    (⨅ i, φ i + ((r : ℝ) : EReal)) =
      (⨅ i, φ i) + ((r : ℝ) : EReal) := by
  have hcancel_neg_add : (((-r : ℝ) : EReal) + ((r : ℝ) : EReal)) = 0 := by
    rw [← EReal.coe_add]
    norm_num
  have hcancel_add_neg : (((r : ℝ) : EReal) + (((-r : ℝ)) : EReal)) = 0 := by
    rw [← EReal.coe_add]
    norm_num
  apply le_antisymm
  · have hshift :
        (⨅ i, φ i + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal) ≤
          ⨅ i, φ i := by
      refine le_iInf fun i => ?_
      have hi : (⨅ i, φ i + ((r : ℝ) : EReal)) ≤ φ i + ((r : ℝ) : EReal) :=
        iInf_le (fun i ↦ φ i + ((r : ℝ) : EReal)) i
      have hi' :
          ((⨅ i, φ i + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal)) +
              ((r : ℝ) : EReal) ≤
            φ i + ((r : ℝ) : EReal) := by
        calc
          ((⨅ i, φ i + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal)) +
              ((r : ℝ) : EReal)
              = ⨅ i, φ i + ((r : ℝ) : EReal) := by
                  rw [add_assoc]
                  rw [hcancel_neg_add]
                  simp
          _ ≤ φ i + ((r : ℝ) : EReal) := hi
      exact (EReal.addLECancellable_coe r).add_le_add_iff_right.mp hi'
    have hshift' :
        (⨅ i, φ i + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal) ≤
          ((⨅ i, φ i) + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal) := by
      calc
        (⨅ i, φ i + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal)
            ≤ ⨅ i, φ i := hshift
        _ = ((⨅ i, φ i) + ((r : ℝ) : EReal)) + (((-r : ℝ)) : EReal) := by
              rw [add_assoc]
              rw [hcancel_add_neg]
              simp
    exact (EReal.addLECancellable_coe (-r)).add_le_add_iff_right.mp hshift'
  · refine le_iInf fun i ↦ add_le_add (iInf_le φ i) le_rfl

/-- Helper for Proposition 25.43: the strong-relative-interior hypothesis provides a dual point
in `effectiveDomain (g∗[hg])` whose adjoint image lies in `effectiveDomain (f∗[hf])`. This is the
common witness needed for both the precomposition and sum `Γ₀` steps. -/
private theorem dualDomainWitnessOfZeroMemSriConjugateDomains :
    (Set.range L.adjoint ∩ effectiveDomain (f∗[hf])).Nonempty ∧
      (effectiveDomain (g∗[hg]) ∩ effectiveDomain ((f∗[hf]) ∘ L.adjoint)).Nonempty := by
  rcases Set.mem_strongRelativeInterior_iff.mp hsri with ⟨hzero, _⟩
  rcases Set.mem_sub.mp hzero with ⟨x, hx, y, hy, hxy⟩
  have hy' : x ∈ L.adjoint '' effectiveDomain (g∗[hg]) := by
    simpa [sub_eq_zero.mp hxy] using hy
  rcases hy' with ⟨u, hu, hxu⟩
  have hxu : L.adjoint u = x := by
    simpa using hxu
  constructor
  · -- Turn the `sri` witness into the range/effective-domain intersection for `L.adjoint`.
    refine ⟨x, ?_, hx⟩
    exact ⟨u, hxu⟩
  · -- The same point `u` lies in the dual effective-domain intersection for the pointwise sum.
    refine ⟨u, hu, ?_⟩
    rw [mem_effectiveDomain_iff, Function.comp, hxu]
    exact mem_effectiveDomain_iff.mp hx

/-- Helper for Proposition 25.43: the dual sum `g∗[hg] + (f∗[hf]) ∘ L.adjoint` belongs to
`Γ₀(K)` under the conjugate-domain regularity hypothesis. -/
private theorem dualPrecompMemGammaZero :
    (f∗[hf]) ∘ L.adjoint ∈ Γ₀(K) := by
  rcases dualDomainWitnessOfZeroMemSriConjugateDomains
      (hf := hf) (hg := hg) (L := L) hsri with ⟨hcompDom, _⟩
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  -- Package the dual precomposition once so later local bridges stay on a stable `Γ₀` surface.
  exact
    precompContinuousLinearMapMemGammaZeroOfRangeInterEffectiveDomainNonempty
      (h := f∗[hf]) (hh := hfConj) (A := L.adjoint) hcompDom

/-- Helper for Proposition 25.43: the conjugate of the dual precomposition is the lower
semicontinuous convex envelope of the Chapter 25 infimal postcomposition `L ▷ f`. -/
private theorem dualPrecompConjugateEqParallelCompositionEnvelope :
    Function.asEReal (((f∗[hf]) ∘ L.adjoint)∗[dualPrecompMemGammaZero (hf := hf) (hg := hg)
      (L := L) (hsri := hsri)]) = lowerSemicontinuousConvexEnvelope (L ▷ f) := by
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  rcases dualDomainWitnessOfZeroMemSriConjugateDomains
      (hf := hf) (hg := hg) (L := L) hsri with ⟨hcompDom, _⟩
  have hdualPrecomp : (f∗[hf]) ∘ L.adjoint ∈ Γ₀(K) :=
    dualPrecompMemGammaZero (hf := hf) (hg := hg) (L := L) (hsri := hsri)
  have hraw :
      Function.asEReal (((f∗[hf]) ∘ L.adjoint)∗[hdualPrecomp]) =
        (Function.asEReal ((f∗[hf]) ∘ L.adjoint))∗ := by
    -- Rewrite the packaged conjugate back to the raw Fenchel conjugate owner.
    funext u
    simpa [Function.asEReal] using
      (gammaZeroConjugate_apply (f := (f∗[hf]) ∘ L.adjoint) (hf := hdualPrecomp) u)
  have hbiconj :
      (f∗[hf]).asEReal∗ = (f : H → EReal) := by
    -- Corollary 13.38 turns the dual biconjugate back into the original `Γ₀` function.
    simpa [gammaZeroConjugate_apply] using biconjugate_eq_of_mem_gammaZero hf
  calc
    Function.asEReal (((f∗[hf]) ∘ L.adjoint)∗[hdualPrecomp])
        = (Function.asEReal ((f∗[hf]) ∘ L.adjoint))∗ := hraw
    _ = ((f∗[hf]).asEReal ∘ L.adjoint)∗ := by
      rfl
    _ =
        lowerSemicontinuousConvexEnvelope
          (((L.adjoint).adjoint ▷ (f∗[hf]).asEReal∗) : K → EReal) := by
      -- Route correction: use Proposition 13.48 directly instead of the unavailable Chapter 15
      -- owner theorem for this precomposition bridge.
      simpa using
        conjugate_comp_eq_lowerSemicontinuousConvexEnvelope_adjointInfimalPostcomposition
          (g := f∗[hf]) (hg := hfConj) (L := L.adjoint) hcompDom
    _ = lowerSemicontinuousConvexEnvelope (L ▷ f) := by
      have hpost :
          (((L.adjoint).adjoint ▷ (f∗[hf]).asEReal∗) : K → EReal) = (L ▷ f) := by
        rw [ContinuousLinearMap.adjoint_adjoint]
        simpa using
          congrArg (fun φ : H → EReal ↦ infimalPostcomposition L φ) hbiconj
      exact congrArg lowerSemicontinuousConvexEnvelope hpost

/-- Helper for Proposition 25.43: the dual sum `g∗[hg] + (f∗[hf]) ∘ L.adjoint` belongs to
`Γ₀(K)` under the conjugate-domain regularity hypothesis. -/
private theorem dualSumMemGammaZeroOfZeroMemSriConjugateDomains :
    g∗[hg] + (f∗[hf]) ∘ L.adjoint ∈ Γ₀(K) := by
  rcases dualDomainWitnessOfZeroMemSriConjugateDomains
      (hf := hf) (hg := hg) (L := L) hsri with ⟨hcompDom, hsumDom⟩
  have hfConj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
  have hgConj : g∗[hg] ∈ Γ₀(K) := gammaZeroConjugate_mem_gammaZero hg
  have hcomp : (f∗[hf]) ∘ L.adjoint ∈ Γ₀(K) :=
    dualPrecompMemGammaZero (hf := hf) (hg := hg) (L := L) (hsri := hsri)
  -- Combine the dual precomposition and dual summand at the witness supplied by `hsri`.
  exact pointwiseAdd_mem_gammaZero (g∗[hg]) ((f∗[hf]) ∘ L.adjoint) hgConj hcomp hsumDom

/- Helper for Proposition 25.43: the swapped-data Theorem 15.27 identifies the conjugate of
`g∗[hg] + (f∗[hf]) ∘ L.adjoint` with `((L ▷ f) □ g)`. -/
omit hsri in
private theorem
    neg_compositePrimalOptimalValue_affineTiltConjugate_eq_dualSumConjugate
    (u : K) :
    -compositePrimalOptimalValue
        (affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) u)
        (f∗[hf]) L.adjoint =
      (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ u := by
  have hzero :
      (affineTiltEReal
          (compositePrimalObjective (g∗[hg]) (f∗[hf]) L.adjoint) u)∗ 0 =
        -compositePrimalOptimalValue
          (affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) u)
          (f∗[hf]) L.adjoint := by
    rw [← tilted_compositePrimalObjective_eq_affineTilt
      (h := g∗[hg]) (hh := gammaZeroConjugate_mem_gammaZero hg)
      (k := f∗[hf]) (A := L.adjoint) (y := u)]
    rw [conjugate_zero_eq_neg_iInf_local, compositePrimalOptimalValue_def, sInf_range]
  calc
    -compositePrimalOptimalValue
        (affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) u)
        (f∗[hf]) L.adjoint
        =
          (affineTiltEReal
            (compositePrimalObjective (g∗[hg]) (f∗[hf]) L.adjoint) u)∗ 0 := by
              exact hzero.symm
    _ = (τ (-u) ((compositePrimalObjective (g∗[hg]) (f∗[hf]) L.adjoint)∗)) 0 := by
          have hconj :=
            congrFun
              (conjugate_translate_add_inner_add_const
                (f := compositePrimalObjective (g∗[hg]) (f∗[hf]) L.adjoint)
                (y := (0 : K)) (v := -u) (β := 0))
              0
          simpa [affineTiltEReal, Pi.add_apply, add_assoc] using hconj
    _ = (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ u := by
          simp [translate_apply, compositePrimalObjective_apply, Function.asEReal_apply]

/-- Helper for Proposition 25.43: each concrete dual point majorizes the primal slice
`((L ▷ f) □ g) u`. -/
private theorem infimalPostcompositionInfimalConvolution_le_affineTiltCompositeDualObjective
    (u : K) (x : H) :
    ((L ▷ f) □ g) u ≤
      compositeDualObjective
        (affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) u)
        (f∗[hf]) L.adjoint x := by
  let tilt :=
    affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) u
  calc
    ((L ▷ f) □ g) u
        ≤ (L ▷ f) (L x) + (g (u - L x) : EReal) := by
            exact iInf_le (fun y : K ↦ (L ▷ f) y + (g (u - y) : EReal)) (L x)
    _ ≤ (f x : EReal) + (g (u - L x) : EReal) := by
          have hpost :
              (L ▷ f) (L x) = sInf ((fun z : H ↦ (f z : EReal)) '' (L ⁻¹' {L x})) := by
            simpa using infimalPostcomposition_apply L f (L x)
          rw [hpost]
          exact add_le_add
            (sInf_le ⟨x, by simp [Set.mem_preimage, Set.mem_singleton_iff], rfl⟩)
            le_rfl
    _ = compositeDualObjective tilt (f∗[hf]) L.adjoint x := by
          rw [compositeDualObjective_apply,
            conjugate_affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg)]
          have hf_biconj :
              (Function.asEReal (f∗[hf]))∗ x = (f x : EReal) := by
            simpa [gammaZeroConjugate_apply] using
              congrFun (biconjugate_eq_of_mem_gammaZero hf) x
          have hg_biconj :
              g.asEReal∗∗ (u - L x) = g.asEReal (u - L x) := by
            simpa using congrFun (biconjugate_eq_of_mem_gammaZero hg) (u - L x)
          rw [ContinuousLinearMap.adjoint_adjoint]
          have hshift : -(L x) - -u = u - L x := by
            abel
          rw [translate_apply, hshift, hf_biconj, hg_biconj]
          simp [tilt, gammaZeroConjugate_apply, add_comm]

/-- Helper for Proposition 25.43: the swapped Corollary 13.25 right-hand side normalizes to the
target infimal-postcomposition/infimal-convolution owner. -/
private theorem swappedDualNormalization
    :
    ((g∗[hg]).asEReal∗) □ (((L.adjoint).adjoint ▷ (f∗[hf]).asEReal∗)) = ((L ▷ f) □ g) := by
  let dualBiconj : K → EReal := (g∗[hg]).asEReal∗
  let primalRaw : K → EReal := g.asEReal
  let swappedPost : K → EReal := ((L.adjoint).adjoint ▷ (f∗[hf]).asEReal∗)
  let primalPost : K → EReal := (L ▷ f)
  -- Normalize the integrand pointwise to avoid a large owner-level `isDefEq` rewrite.
  ext u
  have hgBiconj :
      ∀ y : K, dualBiconj y = primalRaw y := by
    intro y
    simpa [dualBiconj, primalRaw, gammaZeroConjugate_apply] using
      congrFun (biconjugate_eq_of_mem_gammaZero hg) y
  have hfBiconj :
      ∀ x : H, (f∗[hf]).asEReal∗ x = f.asEReal x := by
    intro x
    simpa [gammaZeroConjugate_apply] using
      congrFun (biconjugate_eq_of_mem_gammaZero hf) x
  have hpost :
      ∀ y : K, swappedPost y = primalPost y := by
    intro y
    dsimp [swappedPost, primalPost]
    rw [ContinuousLinearMap.adjoint_adjoint]
    simpa using
      congrFun
        (congrArg (fun φ : H → EReal ↦ infimalPostcomposition L φ)
          (funext hfBiconj))
        y
  have hnormalized :
      (⨅ y : K, dualBiconj y + swappedPost (u - y)) =
        ⨅ y : K, primalRaw y + primalPost (u - y) := by
    refine iInf_congr ?_
    intro y
    rw [hgBiconj y, hpost (u - y)]
  have hcomm :
      (⨅ y : K, primalRaw y + primalPost (u - y)) =
        (⨅ y : K, primalPost y + primalRaw (u - y)) := by
    simpa [primalRaw, primalPost, infimalConvolution_apply] using
      congrFun (infimalConvolution_comm g.asEReal (L ▷ f)) u
  simpa [dualBiconj, primalRaw, swappedPost, primalPost, infimalConvolution_apply] using
    hnormalized.trans hcomm

/-- Helper for Proposition 25.43: Corollary 13.25 on the swapped dual data yields the forward
inequality toward the primal infimal convolution. -/
private theorem swappedDualConjugateLeInfimalPostcompositionInfimalConvolution
    :
    (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ ≤ ((L ▷ f) □ g) := by
  -- Route correction: consume Corollary 13.25 after a single owner-level normalization.
  calc
    (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗
        ≤ ((g∗[hg]).asEReal∗) □ (((L.adjoint).adjoint ▷ (f∗[hf]).asEReal∗)) := by
            simpa [Function.asEReal_apply] using
              conjugate_add_comp_le_infimalConvolution_infimalPostcomposition_adjoint_conjugate
                (f := g∗[hg]) (g := f∗[hf]) (L := L.adjoint)
    _ = ((L ▷ f) □ g) :=
          swappedDualNormalization (hf := hf) (hg := hg) (L := L) (hsri := hsri)

/-- Helper for Proposition 25.43: an attained minimizer of the tilted dual objective yields the
reverse inequality from the primal infimal convolution to the dual conjugate. -/
private theorem infimalPostcompositionInfimalConvolution_le_dualSumConjugate
    (u : K) :
    ((L ▷ f) □ g) u ≤
      (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ u := by
  let tilt :=
    affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) u
  have htilt :
      tilt ∈ Γ₀(K) := by
    simpa [tilt] using
      affine_tilt_mem_gammaZero (h := g∗[hg])
        (hh := gammaZeroConjugate_mem_gammaZero hg) u
  have hsri_tilt :
      (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - L.adjoint '' effectiveDomain tilt) := by
    simpa [tilt, effectiveDomain_affineTiltIoi] using hsri
  obtain ⟨x, hxArg, hxEq⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      tilt htilt (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf) L.adjoint hsri_tilt
  have hxDual :
      compositeDualObjective tilt (f∗[hf]) L.adjoint x =
        -compositePrimalOptimalValue tilt (f∗[hf]) L.adjoint := by
    simpa using (congrArg Neg.neg hxEq).symm
  -- The tilted dual point dominates the primal slice, and attainment converts it back.
  calc
    ((L ▷ f) □ g) u
        ≤ compositeDualObjective tilt (f∗[hf]) L.adjoint x := by
            exact
              infimalPostcompositionInfimalConvolution_le_affineTiltCompositeDualObjective
                (hf := hf) (hg := hg) (L := L) (hsri := hsri) u x
    _ = -compositePrimalOptimalValue tilt (f∗[hf]) L.adjoint := hxDual
    _ = (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ u := by
          simpa [tilt] using
            neg_compositePrimalOptimalValue_affineTiltConjugate_eq_dualSumConjugate
              (hf := hf) (hg := hg) (L := L) (u := u)

private theorem dualSumConjugateEqInfimalPostcompositionInfimalConvolution
    :
    (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ = (L ▷ f) □ g := by
  -- Route correction: separate the swapped-data normalization from the two pointwise inequalities.
  ext u
  apply le_antisymm
  · exact
      swappedDualConjugateLeInfimalPostcompositionInfimalConvolution
        (hf := hf) (hg := hg) (L := L) (hsri := hsri) u
  · exact
      infimalPostcompositionInfimalConvolution_le_dualSumConjugate
        (hf := hf) (hg := hg) (L := L) (hsri := hsri) u

/-- Helper for Proposition 25.43: each primal value `((L ▷ f) □ g) y` is realized by an exact
split through some `x` with `L x` on the infimal-postcomposition side. -/
private theorem exists_exactSplit_infimalPostcomposition_infimalConvolution
    (y : K) (hyDom : y ∈ dom (((L ▷ f) □ g) : K → EReal)) :
    ∃ x : H,
      (L ▷ f) (L x) = (f x : EReal) ∧
        ((L ▷ f) □ g) y = (f x : EReal) + (g (y - L x) : EReal) := by
  let tilt :=
    affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg) y
  have htilt :
      tilt ∈ Γ₀(K) := by
    simpa [tilt] using
      affine_tilt_mem_gammaZero (h := g∗[hg])
        (hh := gammaZeroConjugate_mem_gammaZero hg) y
  have hsri_tilt :
      (0 : H) ∈ sri (effectiveDomain (f∗[hf]) - L.adjoint '' effectiveDomain tilt) := by
    simpa [tilt, effectiveDomain_affineTiltIoi] using hsri
  obtain ⟨x, hxArg, hxEq⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      tilt htilt (f∗[hf]) (gammaZeroConjugate_mem_gammaZero hf) L.adjoint hsri_tilt
  have hsplit :
      ((L ▷ f) □ g) y = (f x : EReal) + (g (y - L x) : EReal) := by
    calc
      ((L ▷ f) □ g) y
          = (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ y := by
              symm
              exact
                congrFun
                  (dualSumConjugateEqInfimalPostcompositionInfimalConvolution
                    (hf := hf) (hg := hg) (L := L) (hsri := hsri))
                  y
      _ = -compositePrimalOptimalValue tilt (f∗[hf]) L.adjoint := by
            simpa [tilt] using
              (neg_compositePrimalOptimalValue_affineTiltConjugate_eq_dualSumConjugate
                (hf := hf) (hg := hg) (L := L) (u := y)).symm
      _ = compositeDualObjective tilt (f∗[hf]) L.adjoint x := by
            rw [hxEq, neg_neg]
      _ = (f x : EReal) + (g (y - L x) : EReal) := by
            rw [compositeDualObjective_apply,
              conjugate_affineTiltIoi (g∗[hg]) (gammaZeroConjugate_mem_gammaZero hg)]
            have hf_biconj :
                (Function.asEReal (f∗[hf]))∗ x = (f x : EReal) := by
              simpa [gammaZeroConjugate_apply] using
                congrFun (biconjugate_eq_of_mem_gammaZero hf) x
            have hg_biconj :
                g.asEReal∗∗ (y - L x) = g.asEReal (y - L x) := by
              simpa using congrFun (biconjugate_eq_of_mem_gammaZero hg) (y - L x)
            rw [ContinuousLinearMap.adjoint_adjoint]
            have hshift : -(L x) - -y = y - L x := by
              abel
            rw [translate_apply, hshift, hf_biconj, hg_biconj]
            simp [tilt, gammaZeroConjugate_apply, add_comm]
  refine ⟨x, ?_, hsplit⟩
  have hpost_le : (L ▷ f) (L x) ≤ (f x : EReal) := by
    have hpost :
        (L ▷ f) (L x) = sInf ((fun z : H ↦ (f z : EReal)) '' (L ⁻¹' {L x})) := by
      simpa using infimalPostcomposition_apply L f (L x)
    rw [hpost]
    exact sInf_le ⟨x, by simp [Set.mem_preimage, Set.mem_singleton_iff], rfl⟩
  have hleft :
      ((L ▷ f) □ g) y ≤ (L ▷ f) (L x) + (g (y - L x) : EReal) := by
    exact iInf_le (fun z : K ↦ (L ▷ f) z + (g (y - z) : EReal)) (L x)
  apply le_antisymm
  · exact hpost_le
  · have hsum_top : (f x : EReal) + (g (y - L x) : EReal) ≠ ⊤ := by
      rw [← hsplit]
      exact lt_top_iff_ne_top.mp hyDom
    have hgy_bot : (g (y - L x) : EReal) ≠ ⊥ := ne_of_gt (g (y - L x)).2
    have hgy_top : (g (y - L x) : EReal) ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top₂ (ne_of_gt (f x).2) hgy_bot).1 hsum_top |>.2
    exact
      (EReal.addLECancellable_coe ((g (y - L x) : EReal).toReal)).add_le_add_iff_right.mp
        (by
          have hineq :
              (f x : EReal) + ((((g (y - L x) : EReal).toReal : ℝ) : EReal)) ≤
                (L ▷ f) (L x) + ((((g (y - L x) : EReal).toReal : ℝ) : EReal)) := by
            simpa [hsplit, add_assoc, EReal.coe_toReal hgy_top hgy_bot] using hleft
          simpa [add_comm, add_left_comm, add_assoc] using hineq)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [CompleteSpace K] hf hg hsri in
/-- Helper for Proposition 25.43: once a split carries a common subgradient for the two
summands, that vector is a subgradient of the infimal convolution at the combined point. -/
private theorem mem_subdifferential_infimalConvolution_ofCommonSubgradient
    {α β : Type*} [CoeTC α EReal] [CoeTC β EReal]
    (F : K → α) (G : K → β) {x y u : K}
    (hF : u ∈ (∂ F) y) (hG : u ∈ (∂ G) (x - y)) :
    u ∈ (∂ (F □ G)) x := by
  have hvalue : (F □ G) x = (F y : EReal) + (G (x - y) : EReal) := by
    rw [mem_subdifferential_iff] at hF hG
    apply le_antisymm
    · rw [infimalConvolution_apply]
      exact iInf_le (fun z : K ↦ (F z : EReal) + (G (x - z) : EReal)) y
    · rw [infimalConvolution_apply]
      refine le_iInf ?_
      intro a
      have hFa : (⟪a - y, u⟫_ℝ : EReal) + (F y : EReal) ≤ (F a : EReal) := hF a
      have hGa :
          (⟪y - a, u⟫_ℝ : EReal) + (G (x - y) : EReal) ≤ (G (x - a) : EReal) := by
        have hGa' := hG (x - a)
        have hrewrite : (x - a) - (x - y) = y - a := by
          abel
        simpa [hrewrite] using hGa'
      have hsum := add_le_add hFa hGa
      have hinner_real : ⟪y - a, u⟫_ℝ + ⟪a - y, u⟫_ℝ = 0 := by
        calc
          ⟪y - a, u⟫_ℝ + ⟪a - y, u⟫_ℝ = ⟪(y - a) + (a - y), u⟫_ℝ := by
            rw [← inner_add_left]
          _ = ⟪(0 : K), u⟫_ℝ := by
            congr 1
            abel
          _ = 0 := by simp
      have hinner :
          (⟪y - a, u⟫_ℝ : EReal) + (⟪a - y, u⟫_ℝ : EReal) = 0 := by
        exact_mod_cast hinner_real
      have hsum' :
          (F y : EReal) + ((G (x - y) : EReal) +
              ((⟪y - a, u⟫_ℝ : EReal) + (⟪a - y, u⟫_ℝ : EReal))) ≤
            (F a : EReal) + (G (x - a) : EReal) := by
        simpa [add_assoc, add_left_comm, add_comm] using hsum
      simpa [hinner, add_assoc] using hsum'
  rw [mem_subdifferential_iff]
  rw [mem_subdifferential_iff] at hF hG
  intro z
  rw [hvalue, infimalConvolution_apply]
  refine le_iInf ?_
  intro a
  have hFa : (⟪a - y, u⟫_ℝ : EReal) + (F y : EReal) ≤ (F a : EReal) := hF a
  have hGa :
      (⟪(z - a) - (x - y), u⟫_ℝ : EReal) + (G (x - y) : EReal) ≤ (G (z - a) : EReal) :=
    hG (z - a)
  have hsum := add_le_add hFa hGa
  have hinner_real :
      ⟪a - y, u⟫_ℝ + ⟪(z - a) - (x - y), u⟫_ℝ = ⟪z - x, u⟫_ℝ := by
    calc
      ⟪a - y, u⟫_ℝ + ⟪(z - a) - (x - y), u⟫_ℝ
          = ⟪(a - y) + ((z - a) - (x - y)), u⟫_ℝ := by
              rw [← inner_add_left]
      _ = ⟪z - x, u⟫_ℝ := by
            congr 1
            abel
  have hinner :
      (⟪a - y, u⟫_ℝ : EReal) + (⟪(z - a) - (x - y), u⟫_ℝ : EReal) =
        (⟪z - x, u⟫_ℝ : EReal) := by
    exact_mod_cast hinner_real
  have hsum' :
      (F y : EReal) + ((G (x - y) : EReal) + (⟪z - x, u⟫_ℝ : EReal)) ≤
        (F a : EReal) + (G (z - a) : EReal) := by
    simpa [hinner, add_assoc, add_left_comm, add_comm] using hsum
  have hbound :
      ((F y : EReal) + (G (x - y) : EReal)) + (⟪z - x, u⟫_ℝ : EReal) ≤
        (F a : EReal) + (G (z - a) : EReal) := by
    simpa [add_assoc] using hsum'
  calc
    (⟪z - x, u⟫_ℝ : EReal) + ((F y : EReal) + (G (x - y) : EReal))
        = ((F y : EReal) + (G (x - y) : EReal)) + (⟪z - x, u⟫_ℝ : EReal) := by
            simp [add_assoc, add_comm]
    _ ≤ (F a : EReal) + (G (z - a) : EReal) := hbound

omit hf hg hsri in
/-- Helper for Proposition 25.43: an exact finite split of an infimal convolution turns any
subgradient of the sum into component subgradients at the two active points. -/
private theorem mem_subdifferential_infimalConvolution_components_of_value_eq
    (F : K → EReal) {x y u : K}
    (hx : x ∈ dom (F □ g))
    (hFy_bot : F y ≠ ⊥)
    (hEq : (F □ g) x = F y + (g (x - y) : EReal))
    (hu : u ∈ (∂ (F □ g)) x) :
    u ∈ (∂ F) y ∧ u ∈ (∂ g) (x - y) := by
  have hsum_top : (F y + (g (x - y) : EReal)) ≠ ⊤ := by
    -- The active split is finite because `x` lies in the domain of `F □ g`.
    rw [← hEq]
    exact ne_of_lt ((mem_dom_iff (F □ g) x).mp hx)
  have hgy_bot : (g (x - y) : EReal) ≠ ⊥ := ne_of_gt (g (x - y)).2
  have hparts := (EReal.add_ne_top_iff_ne_top₂ hFy_bot hgy_bot).1 hsum_top
  have hFy_top : F y ≠ ⊤ := hparts.1
  have hgy_top : (g (x - y) : EReal) ≠ ⊤ := hparts.2
  rw [mem_subdifferential_iff] at hu
  constructor
  · rw [mem_subdifferential_iff]
    intro a
    -- Freeze the `g`-summand and transport the global subgradient inequality to `F`.
    have htranslate : a + (x - y) - x = a - y := by
      abel
    have hu_shift :
        (⟪a + (x - y) - x, u⟫_ℝ : EReal) + (F □ g) x ≤
          (F □ g) (a + (x - y)) :=
      hu (a + (x - y))
    have hupper :
        (F □ g) (a + (x - y)) ≤ (F a : EReal) + (g (x - y) : EReal) := by
      have hfreeze : a + (x - y) - a = x - y := by
        abel
      rw [infimalConvolution_apply]
      simpa [hfreeze] using
        (iInf_le (fun z : K ↦ (F z : EReal) + (g (a + (x - y) - z) : EReal)) a)
    have hraw :
        (⟪a - y, u⟫_ℝ : EReal) + (F y + (g (x - y) : EReal)) ≤
          (F a : EReal) + (g (x - y) : EReal) := by
      have hle := le_trans hu_shift hupper
      simpa [hEq, htranslate, add_assoc, add_left_comm, add_comm] using hle
    rw [← EReal.coe_toReal hgy_top hgy_bot] at hraw
    have hshift :
        ((⟪a - y, u⟫_ℝ : EReal) + F y) +
            (((g (x - y) : EReal).toReal : ℝ) : EReal) ≤
          (F a : EReal) + (((g (x - y) : EReal).toReal : ℝ) : EReal) := by
      simpa [add_assoc] using hraw
    exact
      (EReal.addLECancellable_coe ((g (x - y) : EReal).toReal)).add_le_add_iff_right.mp hshift
  · rw [mem_subdifferential_iff]
    intro b
    -- Freeze the `F`-summand and transport the same inequality to `g`.
    have htranslate : y + b - x = b - (x - y) := by
      abel
    have hu_shift :
        (⟪y + b - x, u⟫_ℝ : EReal) + (F □ g) x ≤ (F □ g) (y + b) :=
      hu (y + b)
    have hupper :
        (F □ g) (y + b) ≤ (F y : EReal) + (g b : EReal) := by
      have hfreeze : y + b - y = b := by
        abel
      rw [infimalConvolution_apply]
      simpa [hfreeze] using
        (iInf_le (fun z : K ↦ (F z : EReal) + (g (y + b - z) : EReal)) y)
    have hraw :
        (⟪b - (x - y), u⟫_ℝ : EReal) + (F y + (g (x - y) : EReal)) ≤
          (F y : EReal) + (g b : EReal) := by
      have hle := le_trans hu_shift hupper
      simpa [hEq, htranslate, add_assoc, add_left_comm, add_comm] using hle
    rw [← EReal.coe_toReal hFy_top hFy_bot] at hraw
    have hshift :
        ((⟪b - (x - y), u⟫_ℝ : EReal) + (g (x - y) : EReal)) +
            (((F y).toReal : ℝ) : EReal) ≤
          (g b : EReal) + (((F y).toReal : ℝ) : EReal) := by
      simpa [add_assoc, add_left_comm, add_comm] using hraw
    exact
      (EReal.addLECancellable_coe ((F y).toReal)).add_le_add_iff_right.mp hshift

omit hsri in
/-- Helper for Proposition 25.43: at an exact infimal-postcomposition point, Proposition 16.60
rewrites membership in `∂ (L ▷ f)` into membership in `∂ f` through `L.adjoint`. -/
private theorem mem_subdifferentialInfimalPostcomposition_image_iff
    {x : H} {u : K} (hEq : (L ▷ f) (L x) = (f x : EReal)) :
    u ∈ (∂ (L ▷ f)) (L x) ↔ L.adjoint u ∈ (∂ f) x := by
  -- Route correction: invoke the owner theorem only after the exact value identity has been
  -- isolated at the concrete point `L x`.
  simpa [Set.mem_preimage] using
    show
      u ∈ (∂ (L ▷ f)) (L x) ↔ u ∈ (L.adjoint) ⁻¹' ((∂ f) x) by
        rw [subdifferential_infimalPostcomposition_eq_preimage_adjoint_of_value_eq
          (f := f) (L := L) (x := x) (y := L x) rfl hEq]

omit hsri hg in
/-- Helper for Proposition 25.43: the Chapter 16 adjoint-image subdifferential for `L.adjoint`
and `f∗[hf]` is exactly the inverse of the Chapter 25 parallel composition `L ▷ ∂ f`. -/
private theorem
    adjointImageSubdifferential_eq_inverse_parallelCompositionSubdifferential :
    ContinuousLinearMap.adjointImageSubdifferential L.adjoint (f∗[hf]) =
      ((((L ▷ ∂ f) : SetValuedOperator K K)⁻¹) : SetValuedOperator K K) := by
  ext y u
  constructor
  · intro hu
    -- Expand the Chapter 16 adjoint-image witness into the Chapter 25 parallel-composition form.
    rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image] at hu
    rw [SetValuedOperator.mem_inverse_iff, ContinuousLinearMap.mem_parallelComposition_iff]
    rcases hu with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [ContinuousLinearMap.adjoint_adjoint] using hx
    · rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf] at hx
      simpa [SetValuedOperator.mem_inverse_iff] using hx
  · intro hu
    -- Read a parallel-composition witness backward as an adjoint-image witness.
    rw [SetValuedOperator.mem_inverse_iff, ContinuousLinearMap.mem_parallelComposition_iff] at hu
    rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image]
    rcases hu with ⟨x, hx, hxsub⟩
    refine ⟨x, ?_, ?_⟩
    · rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate (f := f) hf]
      simpa [SetValuedOperator.mem_inverse_iff] using hxsub
    · simpa [ContinuousLinearMap.adjoint_adjoint] using hx

/-- Clause (i) of Proposition 25.43: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
`0 ∈ sri (dom f^* - L^* (dom g^*))`, then `((L ▷ f) □ g)` is proper, convex, and lower
semicontinuous. In the project's raw `EReal` owner, this is recorded as
`IsProper (((L ▷ f) □ g) : K → EReal)` together with membership in `gamma K`. -/
theorem
    isProper_and_mem_gamma_infimalPostcomposition_infimalConvolution_of_zero_mem_sri_conjugateDomains :
    IsProper ((L ▷ f) □ g) ∧
      ((L ▷ f) □ g) ∈ gamma K := by
  have hdual :
      g∗[hg] + (f∗[hf]) ∘ L.adjoint ∈ Γ₀(K) :=
    dualSumMemGammaZeroOfZeroMemSriConjugateDomains (hf := hf) (hg := hg) (L := L) hsri
  have hrepr :
      Function.asEReal ((g∗[hg] + (f∗[hf]) ∘ L.adjoint)∗[hdual]) = (L ▷ f) □ g := by
    -- Convert the packaged dual conjugate back to the raw owner, then use the normalized formula.
    calc
      Function.asEReal ((g∗[hg] + (f∗[hf]) ∘ L.adjoint)∗[hdual])
          = (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint))∗ := by
              funext v
              simp [Function.asEReal]
      _ = (L ▷ f) □ g := by
        exact
          dualSumConjugateEqInfimalPostcompositionInfimalConvolution
            (hf := hf) (hg := hg) (L := L) (hsri := hsri)
  have hproperConj : IsProper (Function.asEReal ((g∗[hg] + (f∗[hf]) ∘ L.adjoint)∗[hdual])) := by
    -- Properness of the dual sum passes to its conjugate by the Chapter 13 owner theorem.
    simpa [gammaZeroConjugate_apply] using
      (conjugate_is_proper_of_mem_gamma
        (isProper_of_mem_gammaZero hdual)
        (asEReal_mem_gamma_of_mem_gammaZero hdual))
  have hgammaConj :
      Function.asEReal ((g∗[hg] + (f∗[hf]) ∘ L.adjoint)∗[hdual]) ∈ gamma K := by
    -- The same dual representation places the conjugate directly in `gamma K`.
    simpa [gammaZeroConjugate_apply] using
      (conjugate_mem_gamma
        (Function.asEReal (g∗[hg] + (f∗[hf]) ∘ L.adjoint)))
  constructor
  · -- Transport properness across the dual-side identification.
    simpa [hrepr] using hproperConj
  · -- Transport the `gamma` conclusion across the same representation.
    simpa [hrepr] using hgammaConj

/-- Clause (ii) of Proposition 25.43: under the same conjugate-domain regularity,
`∂ (((L ▷ f) □ g)) = (L ▷ ∂ f) □ ∂ g`. -/
theorem
    subdifferential_infimalPostcomposition_infimalConvolution_eq_parallelSum_of_zero_mem_sri_conjugateDomains
    :
    ∂ ((L ▷ f) □ g) =
      (L ▷ ∂ f) □ ∂ g := by
  ext y u
  constructor
  · intro hu
    have hproper :
        IsProper ((L ▷ f) □ g) :=
      (isProper_and_mem_gamma_infimalPostcomposition_infimalConvolution_of_zero_mem_sri_conjugateDomains
          (hf := hf) (hg := hg) (L := L) hsri).1
    let F0 : K → Set.Ioi (⊥ : EReal) := properIoi (((L ▷ f) □ g) : K → EReal) hproper
    have hu0 : u ∈ (∂ F0) y := by
      simpa [F0] using hu
    have hyEff : y ∈ effectiveDomain F0 :=
      subdifferential_domain_subset_effectiveDomain F0 hproper.2
        (by
          rw [SetValuedOperator.mem_dom_iff]
          exact ⟨u, hu0⟩)
    have hyDom : y ∈ dom (((L ▷ f) □ g) : K → EReal) := by
      rw [mem_dom_iff]
      simpa [F0] using (mem_effectiveDomain_iff.mp hyEff)
    rcases exists_exactSplit_infimalPostcomposition_infimalConvolution
        (hf := hf) (hg := hg) (L := L) (hsri := hsri) y hyDom with
      ⟨x, hxPost, hxSplit⟩
    have hxPost_bot : (L ▷ f) (L x) ≠ ⊥ := by
      rw [hxPost]
      exact ne_of_gt (f x).2
    have hxSplit' :
        ((L ▷ f) □ g) y = (L ▷ f) (L x) + (g (y - L x) : EReal) := by
      rw [hxPost]
      exact hxSplit
    rcases
        mem_subdifferential_infimalConvolution_components_of_value_eq
          (g := g) (F := (L ▷ f)) (x := y) (y := L x) (u := u)
          hyDom hxPost_bot hxSplit' hu with
      ⟨huPost, huG⟩
    have huF : L.adjoint u ∈ (∂ f) x :=
      (mem_subdifferentialInfimalPostcomposition_image_iff
        (hf := hf) (hg := hg) (L := L) (x := x) (u := u) hxPost).1 huPost
    have huParallel : u ∈ ((L ▷ ∂ f) : SetValuedOperator K K) (L x) := by
      rw [ContinuousLinearMap.mem_parallelComposition_iff]
      exact ⟨x, rfl, huF⟩
    rw [SetValuedOperator.mem_parallelSum_iff]
    refine ⟨L x, ?_, y - L x, ?_, ?_⟩
    · rw [SetValuedOperator.mem_inverse_iff]
      exact huParallel
    · rw [SetValuedOperator.mem_inverse_iff]
      exact huG
    · abel
  · intro hu
    rw [SetValuedOperator.mem_parallelSum_iff] at hu
    rcases hu with ⟨y₁, hy₁, y₂, hy₂, hySum⟩
    rw [SetValuedOperator.mem_inverse_iff] at hy₁ hy₂
    rcases (ContinuousLinearMap.mem_parallelComposition_iff
      (L := L) (A := ∂ f) (y := y₁) (u := u)).1 hy₁ with ⟨x, hxL, hxSub⟩
    have hxPost :
        (L ▷ f) (L x) = (f x : EReal) :=
      infimalPostcomposition_eq_of_adjoint_mem_subdifferential
        (f := f) (L := L) (x := x) (y := L x) u rfl hxSub
    have huPost :
        u ∈ (∂ (L ▷ f)) (L x) :=
      (mem_subdifferentialInfimalPostcomposition_image_iff
        (hf := hf) (hg := hg) (L := L) (x := x) (u := u) hxPost).2 hxSub
    have hy₂' : u ∈ (∂ g) (y - L x) := by
      have hshift : y - L x = y₂ := by
        rw [← hySum, hxL]
        simp [sub_eq_add_neg, add_assoc]
      simpa [hshift] using hy₂
    simpa [hxL, hySum] using
      mem_subdifferential_infimalConvolution_ofCommonSubgradient
        (F := (L ▷ f)) (G := g) (x := y) (y := L x) (u := u) huPost hy₂'

/-- Proposition 25.43. Under `0 ∈ sri (dom f^* - L^* (dom g^*))`, the infimal
postcomposition/infimal-convolution composite `((L ▷ f) □ g)` is proper, convex, and lower
semicontinuous, and its subdifferential is `(L ▷ ∂ f) □ ∂ g`. -/
theorem infimalPostcomposition_infimalConvolution_regular_and_subdifferential_eq_parallelSum_of_zero_mem_sri_conjugateDomains :
    (IsProper ((L ▷ f) □ g) ∧
      ((L ▷ f) □ g) ∈ gamma K) ∧
      ∂ ((L ▷ f) □ g) =
        (L ▷ ∂ f) □ ∂ g := by
  constructor
  · exact
      isProper_and_mem_gamma_infimalPostcomposition_infimalConvolution_of_zero_mem_sri_conjugateDomains
        (hf := hf) (hg := hg) (L := L) hsri
  · exact
      subdifferential_infimalPostcomposition_infimalConvolution_eq_parallelSum_of_zero_mem_sri_conjugateDomains
        (hf := hf) (hg := hg) (L := L) (hsri := hsri)

end ERealFunction
