import BauschkeLean.Chap06.Definition_6_9
import BauschkeLean.Chap06.Proposition_6_4
import BauschkeLean.Chap06.Proposition_6_21
import BauschkeLean.Chap11.Definition_11_3
import BauschkeLean.Chap12.Definition_12_20
import BauschkeLean.Chap12.Definition_12_23
import BauschkeLean.Chap12.ProximityOperator
import BauschkeLean.Chap12.Proposition_12_22
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap14.Proposition_14_1
import BauschkeLean.Chap14.Remark_14_4
import BauschkeLean.Chap15.Theorem_15_23
import BauschkeLean.Chap09.Definition_9_12
import BauschkeLean.Chap19.Definition_19_11
import BauschkeLean.Chap19.Proposition_19_4
import BauschkeLean.Chap19.Proposition_19_20

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

noncomputable section

universe u v

namespace ERealFunction

section MoreauEnvelopeHelpers

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 19.5: the `γ`-Moreau envelope is the value at the scaled proximal
point plus the textbook quadratic correction. -/
private theorem moreauEnvelope_eq_proxValue_add_scaled_sqDist_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    ({}^[γ] f) x =
      (f (Prox[γ, f, hf] x) : EReal) +
        ((((‖x - Prox[γ, f, hf] x‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
  let p := Prox[γ, f, hf] x
  have hone : γ * (1 : PosReal) = γ := by
    ext
    simp
  have hscale := congrArg (fun g : H → EReal ↦ g x)
    (moreauEnvelope_smul_eq_smul_moreauEnvelope f γ (1 : PosReal))
  have hscale' : {}^[(1 : PosReal)] (γ • f) x = (γ : EReal) * ({}^[γ] f) x := by
    simpa [hone, smul_eq_mul] using hscale
  have hprox : IsProxPoint (γ • f) x p := by
    simpa [p] using
      proximityOperator_isProxPoint
        (γ • f)
        (hasUniqueProxPoint_of_mem_gammaZero (γ • f) (smul_mem_gammaZero f hf γ))
        x
  have hunit := (isProxPoint_iff_moreauEnvelope_eq (γ • f) x p).mp hprox
  have hγ_pos_real : 0 < (γ : ℝ) := γ.2
  have hγ_ne_zero_real : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos_real
  have hγ_pos : 0 < (γ : EReal) := by
    exact_mod_cast hγ_pos_real
  have hγ_ne_zero : (γ : EReal) ≠ 0 := ne_of_gt hγ_pos
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := by
    simp
  have hscaled :
      (γ : EReal) * ({}^[γ] f) x =
        (γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
    calc
      (γ : EReal) * ({}^[γ] f) x = {}^[(1 : PosReal)] (γ • f) x := hscale'.symm
      _ = ((γ • f) p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := hunit
      _ = (γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) := by
        simp
  calc
    ({}^[γ] f) x = (γ : EReal) * (({}^[γ] f) x / (γ : EReal)) := by
      symm
      exact EReal.mul_div_cancel (show (γ : EReal) ≠ ⊥ by simp) hγ_ne_top hγ_ne_zero
    _ = ((γ : EReal) * ({}^[γ] f) x) / (γ : EReal) := by
      rw [EReal.mul_div]
    _ =
        ((γ : EReal) * (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal))) /
          (γ : EReal) := by
      rw [hscaled]
    _ =
        ((γ : EReal) * (f p : EReal)) / (γ : EReal) +
          ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) / (γ : EReal) := by
      rw [EReal.add_div_of_nonneg_right (le_of_lt hγ_pos)]
    _ = (f p : EReal) + ((((1 / 2 : ℝ) * ‖x - p‖ ^ 2 : ℝ) : EReal)) / (γ : EReal) := by
      rw [← EReal.mul_div]
      rw [EReal.mul_div_cancel (show (γ : EReal) ≠ ⊥ by simp) hγ_ne_top hγ_ne_zero]
    _ = (f p : EReal) + ((((‖x - p‖ ^ 2) / (2 * (γ : ℝ)) : ℝ) : EReal)) := by
      rw [← EReal.coe_div]
      ring_nf

end MoreauEnvelopeHelpers

/-- Helper for Proposition 19 5: the canonical composite perturbation
`(x, y) ↦ f x + g (L x + y)`. -/
private abbrev proximalCompositePerturbationFunctionCore
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) :
    H × K → Set.Ioi (⊥ : EReal) :=
  (f ∘ Prod.fst) + (g ∘ fun p ↦ L p.1 + p.2)

/-- The Proposition 19.5 primal objective
`x ↦ φ x + ψ (L x - r) + (1 / 2) ‖x - z‖²`. -/
abbrev proximalCompositePrimalObjective
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (φ : H → Set.Ioi (⊥ : EReal)) (ψ : K → Set.Ioi (⊥ : EReal))
    (z : H) (r : K) (L : H →L[ℝ] K) : H → EReal :=
  fun x ↦
    (φ x : EReal) + (ψ (L x - r) : EReal) +
      ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))

/-- Evaluating `proximalCompositePrimalObjective φ ψ z r L` gives the textbook
Proposition 19.5 primal formula. -/
@[simp] theorem proximalCompositePrimalObjective_apply
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    (φ : H → Set.Ioi (⊥ : EReal)) (ψ : K → Set.Ioi (⊥ : EReal))
    (z : H) (r : K) (L : H →L[ℝ] K) (x : H) :
    proximalCompositePrimalObjective φ ψ z r L x =
      (φ x : EReal) + (ψ (L x - r) : EReal) +
        ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) := rfl

/-- The Proposition 19.5 dual objective
`v ↦ (1 / 2) ‖z - L^* v‖² - {}¹φ(z - L^* v) + ψ^*(v) + ⟪v, r⟫`. -/
abbrev proximalCompositeDualObjective
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (φ : H → Set.Ioi (⊥ : EReal))
    (ψ : K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K) : K → EReal :=
  fun v ↦
    ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
      ({}^[(1 : PosReal)] φ) (z - L.adjoint v)) +
        (ψ∗[hψ] v : EReal) +
          ((⟪v, r⟫_ℝ : ℝ) : EReal)

/-- Evaluating `proximalCompositeDualObjective φ ψ hψ z r L` gives the textbook
Proposition 19.5 dual formula. -/
@[simp] theorem proximalCompositeDualObjective_apply
    {H : Type u} {K : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (φ : H → Set.Ioi (⊥ : EReal))
    (ψ : K → Set.Ioi (⊥ : EReal)) (hψ : ψ ∈ Γ₀(K))
    (z : H) (r : K) (L : H →L[ℝ] K) (v : K) :
    proximalCompositeDualObjective φ ψ hψ z r L v =
      ((((1 / 2 : ℝ) * ‖z - L.adjoint v‖ ^ 2 : ℝ) : EReal) -
        ({}^[(1 : PosReal)] φ) (z - L.adjoint v)) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := rfl

section Basic

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]
variable (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
variable (ψ : K → Set.Ioi (⊥ : EReal))
variable (z : H) (r : K) (L : H →L[ℝ] K)

/- Source/core/bridge triage:
- `source-facing`: Proposition 19.5 is the perturbation attached to the proximal composite
  objective `x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²`.
- `core/canonical`: the owner abstractions are `properIoi`, `compositePerturbationFunction`,
  `perturbationPrimalObjective`, `perturbationDualObjective`, and `Prox[φ, hφ]`.
- `bridge/view`: the formula lemmas below rewrite the owner perturbation back to the textbook
  primal and dual expressions. -/

-- Proof sketch: `proximalObjective φ z` never takes the value `⊥`, and it is finite at `z`.
omit [CompleteSpace H] in
/-- Helper for Proposition 19 5: the proximal objective is proper as an `EReal`-valued map. -/
private theorem isProper_proximalObjective
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H)) (z : H) :
    IsProper (proximalObjective φ z) := by
  constructor
  · -- The proximal objective is a finite real quadratic correction added to an `]-∞,+∞]` value.
    intro x
    exact EReal.add_ne_bot_iff.2 ⟨ne_of_gt (φ x).2, EReal.coe_ne_bot _⟩
  · -- Any finite point of `φ` stays finite after adding the quadratic penalty.
    rcases hφ.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_dom_iff, proximalObjective]
    exact EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top _)

local notation "proximalCompositePerturbation" =>
  proximalCompositePerturbationFunctionCore
    (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z))
    (ψ ∘ fun y ↦ y - r) L

-- Proof sketch: specialize the Chapter 19.20 owner theorem for
-- `compositePerturbationFunction`, then rewrite the specialized composite primal objective into
-- the textbook formula `x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²`.
/-- The primal objective attached to the canonical composite perturbation specialization from
Proposition 19.5 is the textbook objective
`x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²`. -/
theorem perturbationPrimalObjective_compositePerturbationFunction_proximalObjective_translate :
    perturbationPrimalObjective proximalCompositePerturbation =
      proximalCompositePrimalObjective φ ψ z r L := by
  funext x
  change
    (proximalCompositePerturbation (x, 0) : EReal) =
      (φ x : EReal) + (ψ (L x - r) : EReal) +
        ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))
  rw [norm_sub_rev]
  simp [proximalObjective, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

end Basic

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
variable {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
variable {ψ : K → Set.Ioi (⊥ : EReal)} (hψ : ψ ∈ Γ₀(K))
variable (z : H) (r : K) (L : H →L[ℝ] K)

local notation "proximalCompositePerturbation" =>
  proximalCompositePerturbationFunctionCore
    (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z))
    (ψ ∘ fun y ↦ y - r) L

/-- Helper for Proposition 19 5: the proximal quadratic correction packaged as an
`]-∞,+∞]`-valued function. -/
private noncomputable def quadraticPenaltyIoi (z : H) : H → Set.Ioi (⊥ : EReal) :=
  (fun y : H ↦ (1 / 2 : ℝ) * ‖z - y‖ ^ 2).toEReal

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 19 5: coercing the packaged quadratic penalty back to `EReal`
recovers the textbook term `(1 / 2) ‖z - y‖²`. -/
@[simp] private theorem quadraticPenaltyIoi_apply
    (z y : H) :
    (quadraticPenaltyIoi (H := H) z y : EReal) =
      ((((1 / 2 : ℝ) * ‖z - y‖ ^ 2 : ℝ) : EReal)) := by
  simp [quadraticPenaltyIoi]

omit [CompleteSpace H] in
/-- Helper for Proposition 19 5: the proximal quadratic correction belongs to `Γ₀(H)`. -/
private theorem quadraticPenaltyIoi_mem_gammaZero
    (z : H) :
    quadraticPenaltyIoi (H := H) z ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha0 ha1
    -- Use convexity of `u ↦ ‖u‖²` and translate it by the base point `z`.
    have hnorm_sq :
        _root_.ConvexOn ℝ (Set.univ : Set H) (fun u : H ↦ ‖u‖ ^ 2) :=
      (strictConvexOn_norm_sq (H := H)).convexOn
    have hquad :
        ‖z - (a • x + (1 - a) • y)‖ ^ 2 ≤
          a * ‖z - x‖ ^ 2 + (1 - a) * ‖z - y‖ ^ 2 := by
      have hrewrite :
          z - (a • x + (1 - a) • y) = a • (z - x) + (1 - a) • (z - y) := by
        calc
          z - (a • x + (1 - a) • y) = (a + (1 - a)) • z - (a • x + (1 - a) • y) := by
            simp
          _ = a • z + (1 - a) • z - (a • x + (1 - a) • y) := by
            rw [add_smul]
          _ = a • (z - x) + (1 - a) • (z - y) := by
            rw [smul_sub, smul_sub]
            abel_nf
      simpa [hrewrite, smul_eq_mul] using
        hnorm_sq.2
          (by simp : z - x ∈ (Set.univ : Set H))
          (by simp : z - y ∈ (Set.univ : Set H))
          ha0
          (sub_nonneg.mpr ha1)
          (by ring)
    have hscaled :
        (1 / 2 : ℝ) * ‖z - (a • x + (1 - a) • y)‖ ^ 2 ≤
          a * ((1 / 2 : ℝ) * ‖z - x‖ ^ 2) + (1 - a) * ((1 / 2 : ℝ) * ‖z - y‖ ^ 2) := by
      nlinarith
    change
      ((((1 / 2 : ℝ) * ‖z - (a • x + (1 - a) • y)‖ ^ 2 : ℝ) : EReal)) ≤
        (((a * ((1 / 2 : ℝ) * ‖z - x‖ ^ 2) +
          (1 - a) * ((1 / 2 : ℝ) * ‖z - y‖ ^ 2) : ℝ) : EReal))
    exact_mod_cast hscaled
  · -- Continuity of the real quadratic representative yields lower semicontinuity after coercion.
    have hcont : Continuous fun y : H ↦ (1 / 2 : ℝ) * ‖z - y‖ ^ 2 := by
      exact continuous_const.mul ((continuous_norm.comp (continuous_const.sub continuous_id)).pow 2)
    simpa [quadraticPenaltyIoi, Function.toEReal_apply] using
      (continuous_coe_real_ereal.comp hcont).lowerSemicontinuous

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 19 5: the proximal quadratic correction is finite everywhere. -/
private theorem effectiveDomain_quadraticPenaltyIoi_eq_univ
    (z : H) :
    effectiveDomain (quadraticPenaltyIoi (H := H) z) = Set.univ := by
  ext y
  simp [quadraticPenaltyIoi]

omit [CompleteSpace H] in
/-- Helper for Proposition 19 5: the proximal first factor belongs to `Γ₀(H)`. -/
private theorem proximal_factor_mem_gammaZero :
    (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)) ∈ Γ₀(H) := by
  -- Route correction: package the source factor exactly as `φ + (1 / 2) ‖z - ·‖²` before any
  -- conjugate or affine-tilt rewrites.
  have hquad : quadraticPenaltyIoi (H := H) z ∈ Γ₀(H) :=
    quadraticPenaltyIoi_mem_gammaZero (H := H) z
  rcases hφ.2.nonempty with ⟨p, hp⟩
  have hdom :
      (effectiveDomain φ ∩ effectiveDomain (quadraticPenaltyIoi (H := H) z)).Nonempty := by
    refine ⟨p, hp, ?_⟩
    simp [effectiveDomain_quadraticPenaltyIoi_eq_univ (H := H) z]
  have hEq :
      properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z) =
        φ + quadraticPenaltyIoi (H := H) z := by
    funext x
    apply Subtype.ext
    simp [quadraticPenaltyIoi, proximalObjective]
  rw [hEq]
  exact pointwiseAdd_mem_gammaZero φ (quadraticPenaltyIoi (H := H) z) hφ hquad hdom

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 19 5: the quadratic regularization does not change the effective
domain of `φ`. -/
private theorem effectiveDomain_proximalObjective_eq_effectiveDomain :
    dom (proximalObjective φ z) = effectiveDomain φ := by
  ext x
  rw [mem_dom_iff, mem_effectiveDomain_iff, proximalObjective]
  constructor
  · intro hx
    by_contra hφx
    have htop : (φ x : EReal) = ⊤ := le_antisymm le_top (not_lt.mp hφx)
    rw [htop, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hx
    exact not_lt_of_ge le_top hx
  · intro hx
    exact EReal.add_lt_top (ne_of_lt hx) (EReal.coe_ne_top _)

/-- Helper for Proposition 19 5: translating `ψ` by `r` preserves `Γ₀(K)`. -/
private theorem translated_factor_mem_gammaZero
    (hψ : ψ ∈ Γ₀(K))
    :
    (ψ ∘ fun y : K ↦ y - r) ∈ Γ₀(K) := by
  -- Route correction: reuse the Chapter 15 translation owner directly with the shift `-r`.
  simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (translate_mem_gammaZero (f := ψ) hψ (-r))

/-- Helper for Proposition 19.5: precomposing a `Γ₀` function with a continuous linear map
preserves `Γ₀` membership when the range meets the effective domain. -/
private theorem precomp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
    {E : Type*} {F : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (g : F → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(F))
    (L : E →L[ℝ] F)
    (hdom : (Set.range L ∩ effectiveDomain g).Nonempty) :
    g ∘ L ∈ Γ₀(E) := by
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · simpa using hg.1.comp L.continuous
  · refine ⟨effectiveDomain_comp_nonempty_of_range_inter_nonempty g L hdom, subset_rfl, ?_⟩
    intro x hx y hy α hα hα_lt_one
    have hx' : L x ∈ effectiveDomain g := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hx
    have hy' : L y ∈ effectiveDomain g := by
      simpa [Function.comp, mem_effectiveDomain_iff] using hy
    simpa [Function.comp, map_add, map_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hg.2.ineq hx' hy' hα hα_lt_one

omit [CompleteSpace K] in
/-- Helper for Proposition 19 5: translating a strong-relative-interior point to the origin turns
the regularity set into the difference with the singleton base point. -/
private theorem zero_mem_strongRelativeInterior_sub_singleton_of_mem_strongRelativeInterior
    {C : Set K} {y : K} (hy : y ∈ sri C) :
    (0 : K) ∈ sri (C - ({y} : Set K)) := by
  -- Recenter the defining cone/span identity at the base point `y`.
  rcases Set.mem_strongRelativeInterior_iff.mp hy with ⟨hyC, hcone⟩
  refine Set.mem_strongRelativeInterior_iff.mpr ⟨?_, ?_⟩
  · refine Set.mem_sub.mpr ?_
    exact ⟨y, hyC, y, by simp, sub_self y⟩
  · simpa using hcone

omit [CompleteSpace K] in
/-- Helper for Proposition 19 5: reflecting a set through the origin reflects its conic hull. -/
private theorem cone_neg_eq_neg_cone {C : Set K}
    (hC_convex : Convex ℝ C) :
    cone (-C) = -cone C := by
  -- For convex sets, both cone descriptions reduce to the canonical Chapter 6 `toCone` owner.
  calc
    cone (-C) = ((hC_convex.neg.toCone (-C) : ConvexCone ℝ K) : Set K) := by
      simpa [Set.cone_def] using (convexCone_hull_eq_toCone (E := K) hC_convex.neg)
    _ = -(((hC_convex.toCone C : ConvexCone ℝ K) : Set K)) := by
      symm
      exact neg_toCone_eq_toCone_neg hC_convex
    _ = -cone C := by
      rw [show cone C = ((hC_convex.toCone C : ConvexCone ℝ K) : Set K) by
        simpa [Set.cone_def] using (convexCone_hull_eq_toCone (E := K) hC_convex)]

omit [CompleteSpace K] in
/-- Helper for Proposition 19 5: reflecting a strong-relative-interior set at the origin preserves
the origin strong-relative-interior witness. -/
private theorem zero_mem_strongRelativeInterior_neg_of_zero_mem_strongRelativeInterior
    {C : Set K} (hC_convex : Convex ℝ C)
    (hzero : (0 : K) ∈ sri C) :
    (0 : K) ∈ sri (-C) := by
  rcases Set.mem_strongRelativeInterior_iff.mp hzero with ⟨hzero_mem, hcone_eq⟩
  have hneg_nonempty : (-C : Set K).Nonempty := by
    refine ⟨0, ?_⟩
    simpa [Set.mem_neg] using hzero_mem
  -- The cone and closed span both commute with negation at the origin.
  refine
    (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
      (E := K) hneg_nonempty hC_convex.neg).2 ?_
  calc
    cone (-C) = -cone C := cone_neg_eq_neg_cone (K := K) hC_convex
    _ = -(((Submodule.span ℝ C).topologicalClosure : Submodule ℝ K) : Set K) := by
      simpa using congrArg Neg.neg hcone_eq
    _ = (((Submodule.span ℝ C).topologicalClosure : Submodule ℝ K) : Set K) := by
      ext x
      constructor
      · intro hx
        simpa using ((Submodule.span ℝ C).topologicalClosure.neg_mem hx)
      · intro hx
        exact ((Submodule.span ℝ C).topologicalClosure.neg_mem hx)
    _ = (((Submodule.span ℝ (-C)).topologicalClosure : Submodule ℝ K) : Set K) := by
      simp [Submodule.span_neg]

omit [InnerProductSpace ℝ K] [CompleteSpace K] in
/-- Helper for Proposition 19 5: translating `ψ` by `r` shifts its effective domain by
the singleton `{-r}`. -/
private theorem effectiveDomain_translated_factor_eq :
    effectiveDomain (ψ ∘ fun y : K ↦ y - r) = effectiveDomain ψ - ({-r} : Set K) := by
  ext y
  constructor
  · intro hy
    -- Recover a domain witness for `ψ` by undoing the translation by `r`.
    rw [mem_effectiveDomain_iff] at hy
    refine Set.mem_sub.mpr ?_
    refine ⟨y - r, ?_, -r, by simp, ?_⟩
    · simpa [Function.comp, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy
    · abel
  · intro hy
    -- A translated domain witness `u ∈ dom ψ` gives `y - r = u`, hence finiteness of `ψ (y - r)`.
    rcases Set.mem_sub.mp hy with ⟨u, hu, v, hv, hy_eq⟩
    rcases Set.mem_singleton_iff.mp hv with rfl
    rw [mem_effectiveDomain_iff]
    have hu_top : (ψ u : EReal) < ⊤ := (mem_effectiveDomain_iff).1 hu
    have hyu : y - r = u := by
      calc
        y - r = (u - -r) - r := by
          have hy_eq' : y = u - -r := by
            simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hy_eq.symm
          rw [hy_eq']
        _ = u := by abel
    simpa [Function.comp, hyu] using hu_top

omit [CompleteSpace H] in
/-- Helper for Proposition 19 5: packaging the proximal objective as `properIoi` does not change
its effective domain. -/
private theorem effectiveDomain_proximal_factor_eq_effectiveDomain :
    effectiveDomain
        (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)) =
      effectiveDomain φ := by
  ext x
  -- Packaging through `properIoi` preserves the finite-value condition defining the domain.
  rw [mem_effectiveDomain_iff, properIoi_apply, ← mem_dom_iff]
  simp [effectiveDomain_proximalObjective_eq_effectiveDomain (φ := φ) (z := z)]

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19 5: the owner translated regularity set is the reflected translate of
the textbook set `L '' effectiveDomain φ - effectiveDomain ψ`. -/
private theorem translated_factor_sub_image_eq_reflect_textbook_domain_set :
    effectiveDomain (ψ ∘ fun y : K ↦ y - r) -
        L '' effectiveDomain
          (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)) =
      -((L '' effectiveDomain φ - effectiveDomain ψ) - ({r} : Set K)) := by
  -- Rewrite both effective domains to the textbook sets, then compare the two sides by witnesses.
  rw [effectiveDomain_translated_factor_eq (ψ := ψ) (r := r),
    effectiveDomain_proximal_factor_eq_effectiveDomain (φ := φ) (hφ := hφ) (z := z)]
  ext y
  constructor
  · intro hy
    rcases Set.mem_sub.mp hy with ⟨u, hu, b, hb, hy_eq⟩
    rcases Set.mem_sub.mp hu with ⟨a, ha, t, ht, hu_eq⟩
    have ht' : t = -r := by simpa using ht
    have hu_eq' : a - -r = u := by simpa [ht'] using hu_eq
    rw [Set.mem_neg]
    refine Set.mem_sub.mpr ?_
    refine ⟨b - a, ?_, r, by simp, ?_⟩
    · exact Set.mem_sub.mpr ⟨b, hb, a, ha, rfl⟩
    · rw [← hu_eq'] at hy_eq
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hy_eq
  · intro hy
    rw [Set.mem_neg] at hy
    rcases Set.mem_sub.mp hy with ⟨w, hw, t, ht, hy_eq⟩
    rcases Set.mem_sub.mp hw with ⟨b, hb, a, ha, hw_eq⟩
    have ht' : t = r := by simpa using ht
    have hy_eq' : (b - a) - r = -y := by simpa [ht', hw_eq] using hy_eq
    refine Set.mem_sub.mpr ?_
    refine ⟨a - -r, ?_, b, hb, ?_⟩
    · exact Set.mem_sub.mpr ⟨a, ha, -r, by simp, rfl⟩
    · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using congrArg Neg.neg hy_eq'

omit [CompleteSpace H] [CompleteSpace K] in
/-- Helper for Proposition 19 5: the textbook regularity hypothesis rewrites to the owner
regularity hypothesis for the translated second factor. -/
private theorem zero_mem_sri_translated_factor_sub_image
    (hψ : ψ ∈ Γ₀(K))
    (hsri : r ∈ sri (L '' effectiveDomain φ - effectiveDomain ψ)) :
    (0 : K) ∈
      sri
        (effectiveDomain (ψ ∘ fun y : K ↦ y - r) -
          L '' effectiveDomain
            (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z))) := by
  -- Recenter the source regularity point `r` at the origin, then reflect to match the owner set.
  let S : Set K := L '' effectiveDomain φ - effectiveDomain ψ
  have hzero_translate :
      (0 : K) ∈ sri (S - ({r} : Set K)) :=
    zero_mem_strongRelativeInterior_sub_singleton_of_mem_strongRelativeInterior
      (C := S) (y := r) hsri
  have hS_convex : Convex ℝ S := by
    exact (hφ.2.convex_effectiveDomain.linear_image L.toLinearMap).sub hψ.2.convex_effectiveDomain
  have htranslate_convex : Convex ℝ (S - ({r} : Set K)) := by
    exact hS_convex.sub (convex_singleton r)
  have hzero_reflect :
      (0 : K) ∈ sri (-((S - ({r} : Set K)))) :=
    zero_mem_strongRelativeInterior_neg_of_zero_mem_strongRelativeInterior
      (K := K) htranslate_convex hzero_translate
  -- The owner regularity set is exactly this reflected translate of the textbook set.
  simpa [S, translated_factor_sub_image_eq_reflect_textbook_domain_set
    (φ := φ) (hφ := hφ) (ψ := ψ) (z := z) (r := r) (L := L)] using hzero_reflect

omit [CompleteSpace K] in
/-- Helper for Proposition 19 5: conjugating the translated second factor
`y ↦ ψ (y - r)` adds the affine correction `⟪·, r⟫`. -/
private theorem translated_factor_conjugate_eq_add_inner
    (v : K) :
    ((ψ ∘ fun y ↦ y - r).asEReal∗ v) =
      (ψ∗[hψ] v : EReal) + ((⟪v, r⟫_ℝ : ℝ) : EReal) := by
  -- The translated factor is `τ r ψ.asEReal`, so Proposition 13.23 adds the dual affine term.
  simpa [gammaZeroConjugate_apply, Function.asEReal_apply, translate_apply, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm, real_inner_comm] using
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := ψ.asEReal) (y := r) (v := (0 : K)) (β := 0))
      v

omit [CompleteSpace H] in
/-- Helper for Proposition 19 5: the proximal objective is the regularized function
`φ + ‖·‖² / 2`, tilted by `x ↦ -⟪x, z⟫`, plus the constant `‖z‖² / 2`. -/
private theorem proximalObjective_eq_add_halfSquaredNorm_add_inner_add_const :
    (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)).asEReal =
      (φ + halfSquaredNorm).asEReal +
        (fun x : H ↦ ((⟪x, -z⟫_ℝ : ℝ) : EReal)) +
        fun _ : H ↦ ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
  funext x
  -- Expand the translated quadratic and regroup the finite affine and constant corrections.
  change (proximalObjective φ z x : EReal) =
    (((φ + halfSquaredNorm).asEReal x + ((⟪x, -z⟫_ℝ : ℝ) : EReal)) +
      ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)))
  rw [proximalObjective, norm_sub_rev]
  have hreal :
      (1 / 2 : ℝ) * ‖x - z‖ ^ 2 =
        (‖x‖ ^ 2) / 2 + ⟪x, -z⟫_ℝ + (‖z‖ ^ 2) / 2 := by
    rw [norm_sub_sq_real]
    simp
    ring
  have hcast :
      ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) =
        (((((‖x‖ ^ 2) / 2 + ⟪x, -z⟫_ℝ + (‖z‖ ^ 2) / 2 : ℝ)) : EReal)) := by
    exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  have hhalf :
      ((φ + halfSquaredNorm).asEReal x : EReal) =
        (φ x : EReal) + ((((‖x‖ ^ 2) / 2 : ℝ) : EReal)) := by
    change (φ x : EReal) + (halfSquaredNorm x : EReal) =
      (φ x : EReal) + ((((‖x‖ ^ 2) / 2 : ℝ) : EReal))
    exact congrArg (fun t : EReal ↦ (φ x : EReal) + t) (halfSquaredNorm_apply x)
  have hsplitE :
      (φ x : EReal) +
          ((((‖x‖ ^ 2) / 2 + ⟪x, -z⟫_ℝ + (‖z‖ ^ 2) / 2 : ℝ)) : EReal) =
        (((φ x : EReal) + ((((‖x‖ ^ 2) / 2 : ℝ) : EReal))) +
          ((⟪x, -z⟫_ℝ : ℝ) : EReal)) +
            ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
    rw [EReal.coe_add, EReal.coe_add]
    ac_rfl
  have hcast' :
      (φ x : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal)) =
        (φ x : EReal) +
          (((((‖x‖ ^ 2) / 2 + ⟪x, -z⟫_ℝ + (‖z‖ ^ 2) / 2 : ℝ)) : EReal)) :=
    congrArg (fun t : EReal ↦ (φ x : EReal) + t) hcast
  rw [hcast']
  rw [hhalf]
  exact hsplitE

/-- Helper for Proposition 19 5: the conjugate of the proximal objective is the unit Moreau
envelope of `φ*`, shifted by `z`, with the constant correction `-‖z‖² / 2`. -/
private theorem proximalObjective_conjugate_eq_unitMoreauEnvelope_conjugate_sub_halfSquaredNorm
    (u : H) :
    ((properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)).asEReal∗ u) =
      ({}^[(1 : PosReal)] (φ∗[hφ])) (z + u) -
        ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
  have htranslate :=
    congrFun
      (conjugate_translate_add_inner_add_const
        (f := (φ + halfSquaredNorm).asEReal) (y := (0 : H)) (v := -z)
        (β := ‖z‖ ^ 2 / 2))
      u
  have hmoreau :
      ((φ + halfSquaredNorm).asEReal∗ (u + z)) =
        ({}^[(1 : PosReal)] (φ∗[hφ])) (u + z) := by
    -- Proposition 14.1 identifies the conjugate of `φ + q` with the unit Moreau envelope of
    -- `φ*`.
    simpa [Pi.smul_apply] using
      congrFun
        (conjugate_add_scaledQuadratic_eq_moreauEnvelope_gammaZeroConjugate
          (f := φ) (hf := hφ) (γ := (1 : PosReal)))
        (u + z)
  calc
    ((properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)).asEReal∗ u) =
        (((φ + halfSquaredNorm).asEReal +
            (fun x : H ↦ ((⟪x, -z⟫_ℝ : ℝ) : EReal)) +
            fun _ : H ↦ ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)))∗ u) := by
          rw [proximalObjective_eq_add_halfSquaredNorm_add_inner_add_const
            (hφ := hφ) (z := z)]
    _ = ((φ + halfSquaredNorm).asEReal∗ (u + z)) -
          ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
          -- Proposition 13.23 transports the affine tilt to the dual side as a translation by
          -- `-z` and the constant `-‖z‖² / 2`.
          simpa [translate_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
            htranslate
    _ = ({}^[(1 : PosReal)] (φ∗[hφ])) (u + z) -
          ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
          rw [hmoreau]
    _ = ({}^[(1 : PosReal)] (φ∗[hφ])) (z + u) -
          ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
          simp [add_comm]

/-- Helper for Proposition 19 5: the exact owner dual translation carries the constant
`-‖z‖² / 2`, which is missing from the current target statements. -/
private theorem
    perturbationDualObjective_proximalComposite_sub_halfSquaredNorm
    :
    perturbationDualObjective proximalCompositePerturbation =
      fun v : K ↦
        ({}^[(1 : PosReal)] (φ∗[hφ])) (z - L.adjoint v) -
          ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := by
  funext v
  -- Specialize the canonical Chapter 19.20 dual formula, then rewrite the two conjugate terms.
  calc
    perturbationDualObjective proximalCompositePerturbation v =
        compositeDualObjective
          (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z))
          (ψ ∘ fun y ↦ y - r) L v := by
          simpa using
            congrFun
              (perturbationDualObjective_compositePerturbationFunction
                (f := properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z))
                (g := ψ ∘ fun y ↦ y - r) (L := L))
              v
    _ =
        ((properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)).asEReal∗
          (-L.adjoint v)) +
          ((ψ ∘ fun y ↦ y - r).asEReal∗ v) := by
            rw [compositeDualObjective_apply]
    _ =
        ({}^[(1 : PosReal)] (φ∗[hφ])) (z - L.adjoint v) -
          ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) := by
            rw [proximalObjective_conjugate_eq_unitMoreauEnvelope_conjugate_sub_halfSquaredNorm
              (hφ := hφ) (z := z) (-L.adjoint v),
              translated_factor_conjugate_eq_add_inner (hψ := hψ) (r := r) v]
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

-- Proof sketch: specialize Proposition 19.20 (3) to the perturbation above, then rewrite the
-- conjugate of the regularized factor as the unit Moreau envelope of `φ*` and the conjugate of
-- the translated factor as `ψ* + ⟪·, r⟫`, using the canonical packaged conjugate `ψ∗[hψ]`.
/-- The dual objective attached to the canonical composite perturbation specialization from
Proposition 19.5 is the textbook formula `(19.9)` up to the additive constant
`-‖z‖² / 2`. -/
theorem perturbationDualObjective_compositePerturbationFunction_proximalObjective_translate :
    perturbationDualObjective proximalCompositePerturbation =
      fun v : K ↦
        ({}^[(1 : PosReal)] (φ∗[hφ])) (z - L.adjoint v) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) -
              ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
  funext v
  -- Reassociate the finite constant from the owner dual formula to the displayed `(19.9)`
  -- surface.
  rw [perturbationDualObjective_proximalComposite_sub_halfSquaredNorm
    (hφ := hφ) (hψ := hψ) (z := z) (r := r) (L := L)]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Proposition 19 5: the unit Moreau envelope of `φ*` is the quadratic term minus
the unit Moreau envelope of `φ`. -/
private theorem unit_conjugateMoreauEnvelope_eq_halfSquaredNorm_sub_unitMoreau_asEReal
    (x : H) :
    ({}^[(1 : PosReal)] (φ∗[hφ])) x =
      ((((1 / 2 : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal)) - ({}^[(1 : PosReal)] φ) x := by
  -- Route correction: use Remark 14.4 directly on `φ`, then solve for the conjugate envelope
  -- instead of rebuilding the heavier Chapter 14 wrapper surface.
  let pφ : H := Prox[φ, hφ] x
  have hpφ : IsProxPoint φ x pφ := by
    simpa [pφ] using
      proximityOperator_isProxPoint φ (hasUniqueProxPoint_of_mem_gammaZero φ hφ) x
  have hobj_pφ_ne_top : proximalObjective φ x pφ ≠ ⊤ := by
    rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hpφ
    rcases hφ.2.nonempty with ⟨y, hy⟩
    have hy_fin : proximalObjective φ x y ≠ ⊤ := by
      rw [proximalObjective]
      exact ne_of_lt (EReal.add_lt_top (ne_of_lt hy) (EReal.coe_ne_top _))
    have hle : proximalObjective φ x pφ ≤ proximalObjective φ x y := hpφ y
    exact fun htop => hy_fin (top_le_iff.mp (htop ▸ hle))
  have hphi_value :
      ({}^[(1 : PosReal)] φ) x =
        (φ pφ : EReal) + ((((‖x - pφ‖ ^ 2) / 2 : ℝ) : EReal)) := by
    simpa [pφ, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (isProxPoint_iff_moreauEnvelope_eq φ x pφ).1 hpφ
  have hphi_top :
      ({}^[(1 : PosReal)] φ) x ≠ ⊤ := by
    rw [hphi_value]
    refine EReal.add_ne_top ?_ (EReal.coe_ne_top _)
    intro htop
    apply hobj_pφ_ne_top
    rw [proximalObjective, htop, EReal.top_add_coe]
  have hphi_bot :
      ({}^[(1 : PosReal)] φ) x ≠ ⊥ := by
    rw [hphi_value]
    refine EReal.add_ne_bot_iff.2 ?_
    constructor
    · exact ne_of_gt (φ pφ).2
    · exact EReal.coe_ne_bot _
  have hsum :
      ({}^[(1 : PosReal)] φ) x +
        ({}^[(1 : PosReal)] (gammaZeroConjugate φ hφ)) x =
          ((((1 / 2 : ℝ) * ‖x‖ ^ 2 : ℝ) : EReal)) := by
    simpa [Function.asEReal_apply, halfSquaredNorm_apply] using
      congrFun
        (moreauEnvelope_add_conjugateMoreauEnvelope_eq_unitMoreauQuadraticKernel
          (f := φ) hφ)
        x
  have hconj_top :
      ({}^[(1 : PosReal)] (gammaZeroConjugate φ hφ)) x ≠ ⊤ := by
    intro htop
    rw [htop, EReal.add_top_of_ne_bot hphi_bot] at hsum
    exact EReal.coe_ne_top _ hsum.symm
  have hconj_bot :
      ({}^[(1 : PosReal)] (gammaZeroConjugate φ hφ)) x ≠ ⊥ := by
    intro hbot
    rw [hbot, EReal.add_bot] at hsum
    exact EReal.coe_ne_bot _ hsum.symm
  apply le_antisymm
  · exact
      (EReal.le_sub_iff_add_le
        (Or.inr (EReal.coe_ne_bot _))
        (Or.inr (EReal.coe_ne_top _))).2 (by simpa [add_comm] using hsum.le)
  · exact
      (EReal.sub_le_iff_le_add
        (Or.inl hphi_bot)
        (Or.inl hphi_top)).2 (by simpa [add_comm] using hsum.ge)

-- Proof sketch: apply the unit-parameter Moreau decomposition identity to `φ` at
-- `z - L.adjoint v`, then substitute the result into the dual formula above.
/-- The Proposition 19.5 dual objective can also be written in the quadratic-minus-Moreau
form `(19.10)` up to the additive constant `-‖z‖² / 2`. -/
theorem
    perturbationDualObjective_proximalComposite_eq_quadratic_sub_moreauEnvelope
    (v : K) :
    perturbationDualObjective proximalCompositePerturbation v =
      proximalCompositeDualObjective φ ψ hψ z r L v -
        ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) := by
  -- Substitute the Remark 14.4 decomposition at `z - L.adjoint v`, then regroup the owner dual
  -- formula into the displayed quadratic-minus-Moreau surface.
  have hunit :=
    unit_conjugateMoreauEnvelope_eq_halfSquaredNorm_sub_unitMoreau_asEReal
      (hφ := hφ) (x := z - L.adjoint v)
  rw [perturbationDualObjective_proximalComposite_sub_halfSquaredNorm
    (hφ := hφ) (hψ := hψ) (z := z) (r := r) (L := L)]
  change
    ({}^[(1 : PosReal)] (φ∗[hφ])) (z - L.adjoint v) -
        ((((‖z‖ ^ 2) / 2 : ℝ) : EReal)) +
          (ψ∗[hψ] v : EReal) +
            ((⟪v, r⟫_ℝ : ℝ) : EReal) =
      proximalCompositeDualObjective φ ψ hψ z r L v -
        ((((‖z‖ ^ 2) / 2 : ℝ) : EReal))
  rw [proximalCompositeDualObjective_apply]
  rw [hunit]
  simp [sub_eq_add_neg, add_left_comm, add_comm]

/-- Helper for Proposition 19 5: Proposition 12.30 applied to `φ*` at unit parameter identifies
the gradient of the unit Moreau envelope of `φ*` with `Prox_φ`. -/
private theorem hasGradientAt_unitMoreauEnvelope_conjugate_toReal
    (x : H) :
    HasGradientAt
      (fun y : H ↦ (({}^[(1 : PosReal)] (φ∗[hφ])) y).toReal)
      (Prox[φ, hφ] x) x := by
  -- Keep the source route on the clean Chapter 14 surface before introducing the later shift by
  -- `z`.
  have hgrad_raw :=
    moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
      (f := gammaZeroConjugate φ hφ)
      (γ := (1 : PosReal))
      (hf := gammaZeroConjugate_mem_gammaZero hφ)
      (x := x)
  have hprox_eq_raw :=
    (congrFun
      (proximityOperator_eq_gradient_conjugateMoreauEnvelope_toReal_of_mem_gammaZero
        (f := φ) (hf := hφ))
      x).trans hgrad_raw.gradient
  simpa [hprox_eq_raw] using hgrad_raw

/-- Helper for Proposition 19 5: translating the unit Moreau envelope of `φ*` by `z` gives the
exact shifted derivative surface needed later in Proposition 19.4. -/
private theorem hasGateauxDerivativeAt_shifted_unitMoreauEnvelope_conjugate_toReal
    (u : H) :
    HasGateauxDerivativeAt
      (fun y : H ↦ (({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)).toReal)
      (InnerProductSpace.toDualMap ℝ H (Prox[φ, hφ] (z + u))) u := by
  -- Compose the unshifted Chapter 14 gradient with the affine map `y ↦ z + y`.
  have hgrad :=
    hasGradientAt_unitMoreauEnvelope_conjugate_toReal (hφ := hφ) (x := z + u)
  have hshift :
      HasFDerivAt
        (fun y : H ↦ (({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)).toReal)
        (InnerProductSpace.toDual ℝ H (Prox[φ, hφ] (z + u)))
        u := by
    simpa [add_comm, add_left_comm, add_assoc] using
      hgrad.hasFDerivAt.comp u (((ContinuousLinearMap.id ℝ H).hasFDerivAt).const_add z)
  simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    hshift.hasGateauxDerivativeAt

/-- Helper for Proposition 19 5: after taking `toReal`, the conjugate of the proximal objective
is the shifted unit Moreau envelope of `φ*` minus the real constant `‖z‖² / 2`. -/
private theorem
    proximalObjective_conjugate_toReal_eq_shifted_unitMoreauEnvelope_conjugate_toReal_sub_const
    :
    (fun y : H ↦
      (((properIoi (proximalObjective φ z)
          (isProper_proximalObjective φ hφ z)).asEReal∗ y)).toReal) =
      fun y : H ↦
        (({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)).toReal - ((‖z‖ ^ 2) / 2 : ℝ) := by
  -- Route correction: separate the `toReal` transport from the later derivative step so the
  -- constant subtraction is handled once and for all here.
  funext y
  let φstar : H → Set.Ioi (⊥ : EReal) := φ∗[hφ]
  let p : H := Prox[φstar, gammaZeroConjugate_mem_gammaZero hφ] (z + y)
  have hp : IsProxPoint φstar (z + y) p := by
    simpa [φstar, p] using
      proximityOperator_isProxPoint
        φstar
        (hasUniqueProxPoint_of_mem_gammaZero φstar (gammaZeroConjugate_mem_gammaZero hφ))
        (z + y)
  have hmoreau_value :
      ({}^[(1 : PosReal)] (φ∗[hφ])) (z + y) =
        ((φ∗[hφ]) p : EReal) +
          ((((‖(z + y) - p‖ ^ 2) / 2 : ℝ) : EReal)) := by
    simpa [φstar, p, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (isProxPoint_iff_moreauEnvelope_eq φstar (z + y) p).1 hp
  have hconj_top :
      ({}^[(1 : PosReal)] (φ∗[hφ])) (z + y) ≠ ⊤ := by
    have hobj_p_ne_top : proximalObjective φstar (z + y) p ≠ ⊤ := by
      rw [IsProxPoint, proximalPoints, mem_argmin_iff, isMinOn_univ_iff] at hp
      rcases (gammaZeroConjugate_mem_gammaZero hφ).2.nonempty with ⟨w, hw⟩
      have hw_fin : proximalObjective φstar (z + y) w ≠ ⊤ := by
        rw [proximalObjective]
        exact ne_of_lt (EReal.add_lt_top (ne_of_lt hw) (EReal.coe_ne_top _))
      have hle : proximalObjective φstar (z + y) p ≤ proximalObjective φstar (z + y) w := hp w
      exact fun htop => hw_fin (top_le_iff.mp (htop ▸ hle))
    rw [hmoreau_value]
    refine EReal.add_ne_top ?_ (EReal.coe_ne_top _)
    intro htop
    apply hobj_p_ne_top
    rw [proximalObjective, htop, EReal.top_add_coe]
  have hconj_bot :
      ({}^[(1 : PosReal)] (φ∗[hφ])) (z + y) ≠ ⊥ := by
    rw [hmoreau_value]
    refine EReal.add_ne_bot_iff.2 ?_
    constructor
    · exact ne_of_gt ((φ∗[hφ]) p).2
    · exact EReal.coe_ne_bot _
  have hraw :=
    proximalObjective_conjugate_eq_unitMoreauEnvelope_conjugate_sub_halfSquaredNorm
      (hφ := hφ) (z := z) y
  have htoReal :
      (((properIoi (proximalObjective φ z)
          (isProper_proximalObjective φ hφ z)).asEReal∗ y)).toReal =
        ((({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)) -
          ((((‖z‖ ^ 2) / 2 : ℝ) : EReal))).toReal := by
    simpa using congrArg EReal.toReal hraw
  rw [EReal.toReal_sub hconj_top hconj_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at htoReal
  simpa using htoReal

/-- Helper for Proposition 19 5: the exact owner conjugate surface required by Proposition 19.4
inherits the shifted unit-Moreau derivative after subtracting the constant `‖z‖² / 2`. -/
private theorem hasGateauxDerivativeAt_proximalObjective_conjugate_toReal
    (u : H) :
    HasGateauxDerivativeAt
      (fun y : H ↦
        (((properIoi (proximalObjective φ z)
            (isProper_proximalObjective φ hφ z)).asEReal∗ y)).toReal)
      (InnerProductSpace.toDualMap ℝ H (Prox[φ, hφ] (z + u))) u := by
  -- Differentiate the shifted Moreau envelope first, then remove the fixed constant from the
  -- owner conjugate formula.
  have hgrad :=
    hasGradientAt_unitMoreauEnvelope_conjugate_toReal (hφ := hφ) (x := z + u)
  have hshift :
      HasFDerivAt
        (fun y : H ↦ (({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)).toReal - ((‖z‖ ^ 2) / 2 : ℝ))
        (InnerProductSpace.toDual ℝ H (Prox[φ, hφ] (z + u)))
        u := by
    have hbase :
        HasFDerivAt
          (fun y : H ↦ (({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)).toReal)
          (InnerProductSpace.toDual ℝ H (Prox[φ, hφ] (z + u)))
          u := by
      simpa [add_comm, add_left_comm, add_assoc] using
        hgrad.hasFDerivAt.comp u (((ContinuousLinearMap.id ℝ H).hasFDerivAt).const_add z)
    simpa using hbase.sub_const (((‖z‖ ^ 2) / 2 : ℝ))
  have hgateaux :
      HasGateauxDerivativeAt
        (fun y : H ↦ (({}^[(1 : PosReal)] (φ∗[hφ])) (z + y)).toReal - ((‖z‖ ^ 2) / 2 : ℝ))
        (InnerProductSpace.toDualMap ℝ H (Prox[φ, hφ] (z + u)))
        u := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
      hshift.hasGateauxDerivativeAt
  rw [proximalObjective_conjugate_toReal_eq_shifted_unitMoreauEnvelope_conjugate_toReal_sub_const
    (hφ := hφ) (z := z)]
  exact hgateaux

/-- Helper for Proposition 19 5: subtracting a fixed real constant does not change a global
argmin set. -/
private theorem argmin_sub_right_constant_eq
    {X : Type*} (f : X → EReal) (c : ℝ) :
    Argmin (fun x ↦ f x - ((c : ℝ) : EReal)) = Argmin f := by
  ext x
  rw [mem_argmin_iff, mem_argmin_iff]
  constructor
  · intro hx
    -- Adding back the same real constant recovers the original global minimum inequalities.
    rw [isMinOn_univ_iff] at hx ⊢
    intro y
    have hshift :
        (f x - ((c : ℝ) : EReal)) + ((c : ℝ) : EReal) ≤
          (f y - ((c : ℝ) : EReal)) + ((c : ℝ) : EReal) :=
      add_le_add_left (hx y) (((c : ℝ) : EReal))
    have hx_cancel :
        (f x - ((c : ℝ) : EReal)) + ((c : ℝ) : EReal) = f x := by
      calc
        (f x - ((c : ℝ) : EReal)) + ((c : ℝ) : EReal)
            = f x + (((-c : ℝ) : EReal) + ((c : ℝ) : EReal)) := by
                simp [sub_eq_add_neg, add_assoc]
        _ = f x + (((-c + c : ℝ) : ℝ) : EReal) := by
              rw [← EReal.coe_add]
        _ = f x + 0 := by simp
        _ = f x := by simp
    have hy_cancel :
        (f y - ((c : ℝ) : EReal)) + ((c : ℝ) : EReal) = f y := by
      calc
        (f y - ((c : ℝ) : EReal)) + ((c : ℝ) : EReal)
            = f y + (((-c : ℝ) : EReal) + ((c : ℝ) : EReal)) := by
                simp [sub_eq_add_neg, add_assoc]
        _ = f y + (((-c + c : ℝ) : ℝ) : EReal) := by
              rw [← EReal.coe_add]
        _ = f y + 0 := by simp
        _ = f y := by simp
    rw [hx_cancel, hy_cancel] at hshift
    exact hshift
  · intro hx
    -- Subtracting a fixed real constant preserves every comparison in the argmin condition.
    rw [isMinOn_univ_iff] at hx ⊢
    intro y
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      add_le_add_right (hx y) (-((c : ℝ) : EReal))

/-- Helper for Proposition 19 5: tilting the proximal factor by the linear form
`x ↦ ⟪x, L^* v⟫` is the same, up to an additive constant, as recentering the proximal objective at
`z - L^* v`. -/
private theorem argmin_tilted_proximal_factor_eq_singleton_proximityOperator
    (v : K) :
    Argmin
        (fun x : H ↦
          (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z) x : EReal) +
            ((⟪x, L.adjoint v⟫_ℝ : ℝ) : EReal)) =
      ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := by
  let a : H := L.adjoint v
  have hrewrite :
      (fun x : H ↦
        (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z) x : EReal) +
          ((⟪x, a⟫_ℝ : ℝ) : EReal)) =
        fun x : H ↦
          proximalObjective φ (z - a) x -
            (((((‖a‖ ^ 2) / 2 - ⟪z, a⟫_ℝ : ℝ)) : EReal)) := by
    funext x
    rw [properIoi_apply, proximalObjective, proximalObjective]
    have hsplit : z - x = ((z - a) - x) + a := by
      simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hinner :
        ⟪(z - a) - x, a⟫_ℝ + ⟪x, a⟫_ℝ = ⟪z, a⟫_ℝ - ‖a‖ ^ 2 := by
      calc
        ⟪(z - a) - x, a⟫_ℝ + ⟪x, a⟫_ℝ = (⟪z - a, a⟫_ℝ - ⟪x, a⟫_ℝ) + ⟪x, a⟫_ℝ := by
            rw [inner_sub_left]
        _ = ⟪z, a⟫_ℝ - ‖a‖ ^ 2 := by
            rw [inner_sub_left, real_inner_self_eq_norm_sq]
            ring
    have hreal :
        (1 / 2 : ℝ) * ‖z - x‖ ^ 2 + ⟪x, a⟫_ℝ =
          (1 / 2 : ℝ) * ‖(z - a) - x‖ ^ 2 -
            (((‖a‖ ^ 2) / 2) - ⟪z, a⟫_ℝ) := by
      rw [hsplit, norm_add_sq_real]
      nlinarith
    have hcast :
        ((((1 / 2 : ℝ) * ‖z - x‖ ^ 2 : ℝ) : EReal)) + ((⟪x, a⟫_ℝ : ℝ) : EReal) =
          ((((1 / 2 : ℝ) * ‖(z - a) - x‖ ^ 2 : ℝ) : EReal)) -
            (((((‖a‖ ^ 2) / 2) - ⟪z, a⟫_ℝ : ℝ) : EReal)) := by
      exact congrArg (fun t : ℝ ↦ (t : EReal)) hreal
    calc
      (φ x : EReal) + ((((1 / 2 : ℝ) * ‖z - x‖ ^ 2 : ℝ) : EReal)) + ((⟪x, a⟫_ℝ : ℝ) : EReal) =
          (φ x : EReal) +
            (((((1 / 2 : ℝ) * ‖z - x‖ ^ 2 : ℝ) : EReal)) + ((⟪x, a⟫_ℝ : ℝ) : EReal)) := by
            rw [add_assoc]
      _ =
          (φ x : EReal) +
            (((((1 / 2 : ℝ) * ‖(z - a) - x‖ ^ 2 : ℝ) : EReal)) -
              (((((‖a‖ ^ 2) / 2) - ⟪z, a⟫_ℝ : ℝ) : EReal))) := by
            exact congrArg (fun t : EReal ↦ (φ x : EReal) + t) hcast
      _ = (φ x : EReal) + ((((1 / 2 : ℝ) * ‖(z - a) - x‖ ^ 2 : ℝ) : EReal)) -
            (((((‖a‖ ^ 2) / 2) - ⟪z, a⟫_ℝ : ℝ) : EReal)) := by
            simp [sub_eq_add_neg, add_assoc]
  calc
    Argmin
        (fun x : H ↦
          (properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z) x : EReal) +
            ((⟪x, L.adjoint v⟫_ℝ : ℝ) : EReal)) =
        Argmin
          (fun x : H ↦
            proximalObjective φ (z - a) x -
              (((((‖a‖ ^ 2) / 2 - ⟪z, a⟫_ℝ : ℝ)) : EReal))) := by
          rw [hrewrite]
    _ = Argmin (proximalObjective φ (z - a)) := by
          exact
            argmin_sub_right_constant_eq
              (f := proximalObjective φ (z - a))
              (c := (‖a‖ ^ 2) / 2 - ⟪z, a⟫_ℝ)
    _ = ({Prox[φ, hφ] (z - a)} : Set H) := by
          apply Set.eq_singleton_iff_unique_mem.2
          constructor
          · exact
              proximityOperator_isProxPoint φ
                (hasUniqueProxPoint_of_mem_gammaZero φ hφ) (z - a)
          · intro x hx
            exact
              eq_proximityOperator_of_isProxPoint φ
                (hasUniqueProxPoint_of_mem_gammaZero φ hφ) hx
    _ = ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := by
          simp [a]

/-- Helper for Proposition 19 5: the public dual surface and the owner perturbation dual
surface have the same argmin set. -/
private theorem argmin_perturbationDualObjective_eq_argmin_proximalCompositeDualObjective :
    Argmin (perturbationDualObjective proximalCompositePerturbation) =
      Argmin (proximalCompositeDualObjective φ ψ hψ z r L) := by
  -- Rewrite the owner dual objective to the public surface plus a fixed constant shift, then
  -- remove that shift from the argmin set.
  calc
    Argmin (perturbationDualObjective proximalCompositePerturbation) =
        Argmin
          (fun v : K ↦
            proximalCompositeDualObjective φ ψ hψ z r L v -
              ((((‖z‖ ^ 2) / 2 : ℝ) : EReal))) := by
          congr 1
          funext v
          exact
            perturbationDualObjective_proximalComposite_eq_quadratic_sub_moreauEnvelope
              (hφ := hφ) (hψ := hψ) (z := z) (r := r) (L := L) v
    _ = Argmin (proximalCompositeDualObjective φ ψ hψ z r L) := by
          simpa using
            argmin_sub_right_constant_eq
              (f := proximalCompositeDualObjective φ ψ hψ z r L)
              (c := ‖z‖ ^ 2 / 2)

/-- Helper for Proposition 19 5: the same zero-centered regularity hypothesis provides a dual
minimizer for the specialized composite objective. -/
private theorem exists_mem_argmin_compositeDualObjective_of_zero_mem_sri
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ v, v ∈ Argmin (compositeDualObjective f g L) ∧
      compositeDualObjective f g L v = -compositePrimalOptimalValue f g L := by
  obtain ⟨a, ha, b, hb, hba⟩ :=
    exists_domain_pair_eq_image_of_zero_mem_sri_sub_image_effectiveDomain
      (f := f) (g := g) (L := L) hsri
  let φ : H → Set.Ioi (⊥ : EReal) := fun x ↦ f (x + a)
  let ψ : K → Set.Ioi (⊥ : EReal) := fun y ↦ g (y + b)
  have htranslate :
      effectiveDomain ψ - L '' effectiveDomain φ = effectiveDomain g - L '' effectiveDomain f ∧
        (0 : H) ∈ effectiveDomain φ ∧
        (0 : K) ∈ effectiveDomain ψ ∧
        ∀ v : K, compositeDualObjective φ ψ L v = compositeDualObjective f g L v := by
    simpa [φ, ψ] using
      translated_composite_data_preserves_regular_set
        (f := f) (g := g) (L := L) (a := a) ha (b := b) hb hba
  rcases htranslate with ⟨hregular_translate, hzeroφ, hzeroψ, hdual_translate⟩
  have hφ_gamma : φ ∈ Γ₀(H) := by
    simpa [φ] using translate_mem_gammaZero (f := f) hf a
  have hψ_gamma : ψ ∈ Γ₀(K) := by
    simpa [ψ] using translate_mem_gammaZero (f := g) hg b
  have hsri_translate : (0 : K) ∈ sri (effectiveDomain ψ - L '' effectiveDomain φ) := by
    rw [hregular_translate]
    exact hsri
  obtain ⟨v, hvArgTranslated, hvEqTranslated⟩ :=
    exists_mem_argmin_compositeDualObjective_of_zero_domains
      φ hφ_gamma ψ hψ_gamma L hsri_translate hzeroφ hzeroψ
  have hdual_funext : compositeDualObjective φ ψ L = compositeDualObjective f g L := by
    simpa [φ, ψ] using
      translated_compositeDualObjective_eq_original_of_image_domain_witness
        (f := f) (g := g) (L := L) (a := a) (b := b) hba
  have hvArg : v ∈ Argmin (compositeDualObjective f g L) := by
    rw [mem_argmin_iff_eq_sInf]
    calc
      compositeDualObjective f g L v = compositeDualObjective φ ψ L v := by
        exact (hdual_translate v).symm
      _ = sInf (Set.range (compositeDualObjective φ ψ L)) := by
        exact mem_argmin_iff_eq_sInf.mp hvArgTranslated
      _ = sInf (Set.range (compositeDualObjective f g L)) := by
        rw [hdual_funext]
  refine ⟨v, hvArg, ?_⟩
  calc
    compositeDualObjective f g L v = compositeDualObjective φ ψ L v := by
      exact (hdual_translate v).symm
    _ = -compositePrimalOptimalValue φ ψ L := by
      have hneg := congrArg Neg.neg hvEqTranslated
      simpa using hneg.symm
    _ = -compositePrimalOptimalValue f g L := by
      congr 1
      simpa [φ, ψ] using
        translated_compositePrimalOptimalValue_eq_original_of_image_domain_witness
          (f := f) (g := g) (L := L) (a := a) (b := b) hba

/-- Helper for Proposition 19 5: the zero-centered Chapter 15 regularity hypothesis yields the
strong duality identity for the specialized composite objective. -/
private theorem composite_strong_duality_of_zero_mem_sri_sub_image
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  obtain ⟨v, hvArg, hvValue⟩ :=
    exists_mem_argmin_compositeDualObjective_of_zero_mem_sri
      (hf := hf) (hg := hg) (L := L) hsri
  have hvOpt : compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    simpa [compositeDualOptimalValue_def] using (mem_argmin_iff_eq_sInf.mp hvArg)
  calc
    compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
      rw [hvValue]
      simp
    _ = -compositeDualOptimalValue f g L := by
      rw [hvOpt]

-- Proof sketch: apply the Chapter 15 strong-duality/dual-attainment owner theorem to the
-- canonical composite perturbation specialization from Proposition 19.5, then use the Chapter 19.4
-- singleton-argmin bridge with the Gâteaux derivative formula for the conjugate of the
-- regularized first factor to identify the unique primal minimizer as `Prox_φ (z - L^* v)`.
/-- Proposition 19.5. If `φ ∈ Γ₀(ℋ)`, `ψ ∈ Γ₀(𝒦)`, and
`r ∈ sri (L (dom φ) - dom ψ)`, then the dual problem
`v ↦ (1 / 2) ‖z - L^* v‖² - {}¹φ(z - L^* v) + ψ^*(v) + ⟪v, r⟫`
has a solution. Moreover, for every dual solution `v`, the unique minimizer of
`x ↦ φ(x) + ψ(Lx - r) + (1 / 2) ‖x - z‖²` is `Prox_φ (z - L^* v)`. The companion bridge theorem
`perturbationDualObjective_compositePerturbationFunction_proximalObjective_translate` records the
equivalent dual formula `(19.9)` with the canonical conjugate surface `ψ∗[hψ]`. -/
theorem argmin_proximalCompositeDual_nonempty_and_argmin_primal_eq_singleton_proximityOperator
    (hsri : r ∈ sri (L '' effectiveDomain φ - effectiveDomain ψ)) :
    (Argmin (proximalCompositeDualObjective φ ψ hψ z r L)).Nonempty ∧
      ∀ {v : K},
        v ∈ Argmin (proximalCompositeDualObjective φ ψ hψ z r L) →
        Argmin (proximalCompositePrimalObjective φ ψ z r L) =
          ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := by
  let f0 : H → Set.Ioi (⊥ : EReal) :=
    properIoi (proximalObjective φ z) (isProper_proximalObjective φ hφ z)
  let g0 : K → Set.Ioi (⊥ : EReal) := ψ ∘ fun y : K ↦ y - r
  have hf0 : f0 ∈ Γ₀(H) := proximal_factor_mem_gammaZero (φ := φ) (hφ := hφ) (z := z)
  have hg0 : g0 ∈ Γ₀(K) := translated_factor_mem_gammaZero (ψ := ψ) (r := r) hψ
  have hsri0 :
      (0 : K) ∈ sri (effectiveDomain g0 - L '' effectiveDomain f0) :=
    zero_mem_sri_translated_factor_sub_image
      (φ := φ) (hφ := hφ) (ψ := ψ) (z := z) (r := r) (L := L) hψ hsri
  have hstrong_owner :
      compositePrimalOptimalValue f0 g0 L = -compositeDualOptimalValue f0 g0 L :=
    composite_strong_duality_of_zero_mem_sri_sub_image
      (hf := hf0) (hg := hg0) (L := L) hsri0
  have howner_dual_eq_pert :
      compositeDualObjective f0 g0 L = perturbationDualObjective proximalCompositePerturbation := by
    -- The owner composite dual surface is exactly the perturbation dual surface for this
    -- specialization.
    symm
    simpa [f0, g0] using
      (perturbationDualObjective_compositePerturbationFunction
        (f := f0) (g := g0) (L := L))
  obtain ⟨v0, hv0_owner, _⟩ :=
    exists_mem_argmin_compositeDualObjective_of_zero_mem_sri
      (hf := hf0) (hg := hg0) (L := L) hsri0
  have hv0_pert :
      v0 ∈ Argmin (perturbationDualObjective proximalCompositePerturbation) := by
    rw [← howner_dual_eq_pert]
    exact hv0_owner
  have hv0_public :
      v0 ∈ Argmin (proximalCompositeDualObjective φ ψ hψ z r L) := by
    rw [← argmin_perturbationDualObjective_eq_argmin_proximalCompositeDualObjective
      (hφ := hφ) (hψ := hψ) (z := z) (r := r) (L := L)]
    exact hv0_pert
  have hsri_mem : r ∈ L '' effectiveDomain φ - effectiveDomain ψ :=
    (Set.mem_strongRelativeInterior_iff.mp hsri).1
  rcases Set.mem_sub.mp hsri_mem with ⟨y0, hy0, u0, hu0, hru0⟩
  rcases hy0 with ⟨x0, hx0, rfl⟩
  have hLx0 : L x0 - r = u0 := by
    calc
      L x0 - r = L x0 - (L x0 - u0) := by simp [hru0]
      _ = u0 := by abel
  have hrange_g0 : (Set.range L ∩ effectiveDomain g0).Nonempty := by
    refine ⟨L x0, ⟨x0, rfl⟩, ?_⟩
    rw [mem_effectiveDomain_iff]
    simpa [g0, hLx0] using (mem_effectiveDomain_iff.mp hu0)
  have hg0_comp : g0 ∘ L ∈ Γ₀(H) :=
    precomp_continuousLinearMap_mem_gammaZero_of_range_inter_effectiveDomain_nonempty
      g0 hg0 L hrange_g0
  have hprimal_factor : φ + (g0 ∘ L) ∈ Γ₀(H) := by
    -- The source primal factor is `x ↦ φ(x) + ψ(Lx - r)`, and the `sri` hypothesis provides a
    -- common effective-domain witness for the sum.
    refine pointwiseAdd_mem_gammaZero φ (g0 ∘ L) hφ hg0_comp ?_
    refine ⟨x0, hx0, ?_⟩
    rw [mem_effectiveDomain_iff]
    simpa [Function.comp, g0, hLx0] using (mem_effectiveDomain_iff.mp hu0)
  have hprimal_public_eq_proximalObjective :
      proximalCompositePrimalObjective φ ψ z r L = proximalObjective (φ + (g0 ∘ L)) z := by
    -- This is the source identity `(19.8) = prox-objective of x ↦ φ(x) + ψ(Lx - r)`.
    funext x
    simp [proximalCompositePrimalObjective, proximalObjective, g0, Function.comp, norm_sub_rev,
      add_left_comm, add_comm]
  have hprimal_nonempty :
      (Argmin (proximalCompositePrimalObjective φ ψ z r L)).Nonempty := by
    -- Definition 12.23 gives a proximal point for the source factor, hence a primal minimizer.
    refine ⟨Prox[φ + (g0 ∘ L), hprimal_factor] z, ?_⟩
    rw [hprimal_public_eq_proximalObjective]
    exact
      proximityOperator_isProxPoint
        (φ + (g0 ∘ L))
        (hasUniqueProxPoint_of_mem_gammaZero (φ + (g0 ∘ L)) hprimal_factor)
        z
  refine ⟨⟨v0, hv0_public⟩, ?_⟩
  intro v hv
  have hv_pert :
      v ∈ Argmin (perturbationDualObjective proximalCompositePerturbation) := by
    rw [← argmin_perturbationDualObjective_eq_argmin_proximalCompositeDualObjective
      (hφ := hφ) (hψ := hψ) (z := z) (r := r) (L := L)] at hv
    exact hv
  have hv_owner :
      v ∈ Argmin (compositeDualObjective f0 g0 L) := by
    rw [howner_dual_eq_pert]
    exact hv_pert
  have hgrad_owner :
      HasGateauxDerivativeAt
        (fun y : H ↦ (f0∗[hf0] y : EReal).toReal)
        (InnerProductSpace.toDualMap ℝ H (Prox[φ, hφ] (z - L.adjoint v)))
        (-L.adjoint v) := by
    -- The Chapter 14 derivative bridge lands on the exact owner conjugate surface from
    -- Proposition 19.4.
    change
      HasGateauxDerivativeAt
        (fun y : H ↦
          (((properIoi (proximalObjective φ z)
              (isProper_proximalObjective φ hφ z)).asEReal∗ y)).toReal)
        (InnerProductSpace.toDualMap ℝ H (Prox[φ, hφ] (z - L.adjoint v)))
        (-L.adjoint v)
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hasGateauxDerivativeAt_proximalObjective_conjugate_toReal
        (hφ := hφ) (z := z) (-L.adjoint v)
  have hprimal_cases_owner :
      Argmin (compositePrimalObjective f0 g0 L) = (∅ : Set H) ∨
        Argmin (compositePrimalObjective f0 g0 L) =
          ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := by
    -- Proposition 19.4 reduces the primal argmin set to the empty-or-singleton dichotomy once
    -- the owner conjugate derivative is available.
    exact
      argmin_eq_empty_or_singleton_of_dual_solution_and_hasGateauxDerivativeAt
        (hf := hf0) (hg := hg0) (L := L) (v := v)
        (xstar := Prox[φ, hφ] (z - L.adjoint v))
        hstrong_owner hv_owner hgrad_owner
  have hprimal_owner_eq_public :
      compositePrimalObjective f0 g0 L = proximalCompositePrimalObjective φ ψ z r L := by
    -- Re-expand the owner primal surface back to the displayed textbook objective `(19.8)`.
    funext x
    simp [f0, g0, compositePrimalObjective, proximalCompositePrimalObjective, proximalObjective,
      Function.comp, norm_sub_rev, add_assoc, add_left_comm, add_comm]
  have hprimal_cases :
      Argmin (proximalCompositePrimalObjective φ ψ z r L) = (∅ : Set H) ∨
        Argmin (proximalCompositePrimalObjective φ ψ z r L) =
          ({Prox[φ, hφ] (z - L.adjoint v)} : Set H) := by
    simpa [hprimal_owner_eq_public] using hprimal_cases_owner
  cases hprimal_cases with
  | inl hempty =>
      rcases hprimal_nonempty with ⟨x, hx⟩
      have : False := by
        rw [hempty] at hx
        exact hx
      exact False.elim this
  | inr hsingleton =>
      exact hsingleton

end PrimalSolutionsViaDualSolutions

end ERealFunction
